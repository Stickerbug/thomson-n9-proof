"""Finite three-existing-PSD-seed convex hull diagnosis, no SDP."""
import time,json,hashlib,ast,itertools,signal
from pathlib import Path
START=time.monotonic()
import numpy as np
from scipy.optimize import linprog,differential_evolution,NonlinearConstraint,minimize
from sharp_boundary_actualf_v3 import random_cond,boundary_points,valid,Compiled
from d12_contact2026_core import exact_candidate,RSTRING
from fractions import Fraction
from certify_three_point_d4 import const,add,scale,mul,mono,permute,diag
ROOT=Path(__file__).parent;OUT=ROOT/'d10_sharpconvex2026_valleycenter_results.json';assert not OUT.exists()
class Budget(Exception):pass
signal.signal(signal.SIGALRM,lambda *x:(_ for _ in ()).throw(Budget('60second hard budget')));signal.alarm(115)
source=ROOT/'sharp_contact_refinement2026_batch3_best_original_data.json';data=json.loads(source.read_text());models=[data['first_batch_original_PSD_seed'],*data['third_batch_original_models']];assert len(models)==3
assert all(s['min_B_eigenvalue']>9e-7 for s in models)
src=ROOT/'sharp_contact_refinement2026_refine.py';tree=ast.parse(src.read_text());node=next(n for n in tree.body if isinstance(n,ast.ClassDef)and n.name=='IndependentActual');ns={'np':np,'itertools':itertools,'DEGREE':10};exec(compile(ast.Module(body=[node],type_ignores=[]),str(src),'exec'),ns)
acts=[ns['IndependentActual']([np.array(a)for a in s['A']],s['c'])for s in models]
valley=json.loads((ROOT/'negative_valley_seed1_2026_summary.json').read_text());cand=np.array([[float(z)for z in p]for p in exact_candidate(Fraction(RSTRING))[0]])
known=np.array([q['center_minimum_sample']for q in valley['valleys'][:3]]+[[-.9655589354,-.4069479195,.5089797407],[-.9993574670,-.0179239136,-.0179239017],[.3727866847,.56,-.0401443734],[-.296937,.422535,.422535],[.56,.56,.56],[-1,0,0],[-1,-.56,.56]])
known=np.vstack([known,json.loads((ROOT/'d10_sharpconvex2026_local_check.json').read_text())['worst']['point']]);points=np.vstack([known,cand]);V=np.column_stack([a(points)for a in acts]);rows=[{'point':p.tolist(),'R':v.tolist(),'Gram':float(1+2*np.prod(p)-p@p),'valid':bool(valid(p)[0])}for p,v in zip(points,V)]
result={'warning':'NUMERICAL DIAGNOSIS ONLY; no exact convex-hull exclusion or kernel-family infeasibility claim','source':str(source),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'model_keys':['first_batch_original_PSD_seed','third_batch_original_models[0]','third_batch_original_models[1]'],'model_min_reduced_eigenvalues':[s['min_B_eigenvalue']for s in models],'model_traces':[s['trace']for s in models],'fixed_point_table':rows,'history':[],'weights_proposal':None}
def save():OUT.write_text(json.dumps(result,indent=2)+'\n')
save();common=[r for r in rows if r['valid'] and max(r['R'])<-1e-8]
if common:
 result['common_negative_witness']=min(common,key=lambda r:max(r['R']));result['stop_reason']='common clearly negative point excludes these three fixed kernels convex hull numerically';result['elapsed_seconds']=time.monotonic()-START;save();signal.alarm(0);print(json.dumps(result),flush=True);raise SystemExit()
# Compile the existing original-A normalization once for efficient 60000-point scans.
u,v,t=(mono(i,1)for i in range(3));a=add(t,scale(mul(u,v),-1));b=mul(add(const(1),scale(mul(u,u),-1)),add(const(1),scale(mul(v,v),-1)));Q=[const(1),a]
for k in range(1,10):Q.append(add(scale(mul(a,Q[-1]),2),scale(mul(b,Q[-2]),-1)))
polys=[]
for model in models:
 kernel={}
 for k in range(11):
  for i in range(11-k):
   for j in range(11-k):kernel=add(kernel,scale(mul(mul(mono(0,i),mono(1,j)),Q[k]),float(model['A'][k][i][j])))
 F=scale(add(*(permute(kernel,pm)for pm in itertools.permutations(range(3)))),1/6);polys.append(add(scale(F,7),*(diag(F,j)for j in range(3)),const(float(model['c']))))
comp=Compiled(polys);co=comp.M.toarray()
def vals(p):
 p=np.atleast_2d(p);return np.vstack([np.sum((2-2*p[j:j+700])**(-.5),axis=1)[:,None]-comp.monomials(p[j:j+700])@co for j in range(0,len(p),700)])

# New hard valley and all contact permutation annuli / CFG joining curves.
contacts=np.unique(np.vstack([cand[:,pm]for pm in itertools.permutations(range(3))]),axis=0)
rng=np.random.default_rng(2026101779)
pc=json.loads((ROOT/'narrowroot2026_pointcheck.json').read_text());newvalley=np.array([float(Fraction(x))for x in pc['point']]);known=np.vstack([newvalley,known]);radii=np.array([1e-5,1e-4,1e-3,1e-2,.03,.05]);dirs=rng.normal(size=(48,3));dirs/=np.linalg.norm(dirs,axis=1)[:,None];dirs=np.vstack([dirs,np.eye(3),-np.eye(3)])
rings=np.vstack([z+r*dirs for z in contacts for r in radii]);rings=rings[valid(rings)]
cc=json.loads((ROOT/'narrowroot2026_coefficients.json').read_text());row=next(q for q in cc['local_centers']if set(q['labels'])==set('CFG'));cfg=np.array([(int(v['lo_numerator'])+int(v['hi_numerator']))/2**385 for v in row['center_intervals']]);perms=np.unique(np.array(list(itertools.permutations(cfg))),axis=0);curves=[]
for x,y in itertools.combinations(perms,2):
 line=x[None,:]+np.linspace(0,1,121)[:,None]*(y-x)[None,:];curves.append(line)
 for rad in [1e-4,1e-3,1e-2]:curves.append(line+rng.normal(size=line.shape)*rad)
curves=np.vstack(curves);curves=curves[valid(curves)]
random=random_cond(60000,rng);boundary=boundary_points(6000,rng);pool=np.vstack([points,known,rings,curves,random,boundary]);V=vals(pool)
# Near-contact tiny R must use original recurrence, not expanded float coefficients.
near=np.min(np.sum((pool[:,None,:]-contacts[None,:,:])**2,axis=2),axis=1)<1e-7
V[near]=np.column_stack([a(pool[near])for a in acts])
def gram(p):p=np.atleast_2d(p);return 1+2*np.prod(p,axis=1)-np.sum(p*p,axis=1)
def dist2(p):return np.min(np.sum((np.atleast_2d(p)[:,None,:]-contacts[None,:,:])**2,axis=2),axis=1)
def gj(z):u,v,t=z;return np.array([2*(v*t-u),2*(u*t-v),2*(u*v-t)])
result.update(new_valley=newvalley.tolist(),annulus_radii=radii.tolist(),contact_permutation_count=len(contacts),annulus_valid_count=len(rings),CFG_curve_count=len(curves),random_count=len(random),boundary_count=len(boundary),history=[],weights_proposal=None)
oldw=np.array([.224438,0,.775562]);
# Independent mp80 original A/c values and true-H loss at the supplied physical point.
import mpmath as mp
mp.mp.dps=80
mpA=[[[[mp.mpf(str(v))for v in row]for row in a]for a in m['A']]for m in models]
def mpF(A,p):
 out=mp.mpf(0)
 for pm in itertools.permutations(range(3)):
  u,v,t=[p[j]for j in pm];aa=t-u*v;bb=(1-u*u)*(1-v*v);Q=[mp.mpf(1),aa]
  for k in range(1,10):Q.append(2*aa*Q[-1]-bb*Q[-2])
  for k,M in enumerate(A):out+=Q[k]*sum((M[i][j]*u**i*v**j for i in range(len(M))for j in range(len(M))),mp.mpf(0))/6
 return out
def mpR(A,c,p):return sum(1/mp.sqrt(2-2*x)for x in p)-c-7*mpF(A,p)-sum(mpF(A,[mp.mpf(1),x,x])for x in p)
def rawmid(v):return mp.mpf(int(v['lo_numerator'])+int(v['hi_numerator']))/mp.mpf(2)**385
mppt=[mp.mpf(Fraction(v).numerator)/Fraction(v).denominator for v in pc['point']];hv=[rawmid(v)for v in cc['H_coefficients_ascending']];loss=sum(1/mp.sqrt(2-2*x)-mp.polyval(list(reversed(hv)),x)for x in mppt);rh=sum(rawmid(c)*mppt[0]**e[0]*mppt[1]**e[1]*mppt[2]**e[2]for e,c in cc['R_coefficients']);rseed=[mpR(a,mp.mpf(str(m['c'])),mppt)for a,m in zip(mpA,models)];result['mp80_supplied_valley']={'original3_truef_R':[str(r)for r in rseed],'oldblend_original_truef_R':str(sum(mp.mpf(str(w))*r for w,r in zip(oldw,rseed))),'newkernel_R_H':str(rh),'Hermite_loss':str(loss),'newkernel_R_f':str(rh+loss),'newkernel_minus_oldblend_truef':str(rh+loss-sum(mp.mpf(str(w))*r for w,r in zip(oldw,rseed)))};save();print('mp supplied',result['mp80_supplied_valley'],flush=True)
# First minimize each seed and the old blend from the newly located valley.
def polish(w,start,steps=120):
 act=ns['IndependentActual']([sum(w[j]*np.array(models[j]['A'][k])for j in range(3))for k in range(11)],sum(w[j]*models[j]['c']for j in range(3)))
 def ob(z):r,g=act(z,True);return float(r[0])*1e7,g[0]*1e7
 opt=minimize(ob,start,jac=True,method='SLSQP',bounds=[(-1,.56)]*3,constraints=[{'type':'ineq','fun':lambda z:float(gram(z)[0]),'jac':gj}],options={'maxiter':steps,'ftol':1e-9});return opt.x,float(act(opt.x)[0])
initial=[]
for w in [np.eye(3)[j]for j in range(3)]+[oldw]:
 if time.monotonic()-START>65:break
 z,r=polish(w,newvalley);initial.append({'weights':w.tolist(),'point':z.tolist(),'truef_R':r,'Gram':float(gram(z)[0])});known=np.vstack([known,z])
result['valley_initial_polishes']=initial;V=np.vstack([V,np.column_stack([a(known)for a in acts])]);pool=np.vstack([pool,known]);save()
try:
 for iteration in range(3):
  if time.monotonic()-START>100:break
  d=dist2(pool);margin=d>=1e-8;den=np.maximum(d,1e-8);Z=V/den[:,None]
  lp=linprog([0,0,0,-1],A_ub=np.column_stack([-Z,margin.astype(float)]),b_ub=np.where(margin,0,2e-13/den),A_eq=[[1,1,1,0]],b_eq=[1],bounds=[(.01,1),(0,1),(0,1),(None,None)],method='highs',options={'time_limit':10,'primal_feasibility_tolerance':1e-9,'dual_feasibility_tolerance':1e-9})
  rr={'round':iteration+1,'LP_success':bool(lp.success),'message':lp.message};result['history'].append(rr)
  if not lp.success:result['stop_reason']='infeasible LP';break
  w=lp.x[:3];ints=np.round(w*1e6).astype(int);ints[np.argmax(ints)]+=1000000-sum(ints);w=ints/1e6;eta=lp.x[3];rr.update(eta=float(eta),weights=w.tolist(),rational_weights=[str(Fraction(int(j),1000000))for j in ints],sample_min_R=float((V@w).min()),sample_min_ratio=float(((V@w)[margin]/d[margin]).min()))
  if eta<=0:result['stop_reason']='nonpositive centered sample margin';break
  # Local starts include ALL newly found valley minima, original known valleys, near-duplicate CFG midpoint.
  starts=np.vstack([newvalley,np.array([a['point']for a in initial]),known[:12],(perms[0]+perms[1])/2]);found=[]
  for z0 in starts:
   if time.monotonic()-START>103:break
   z,r=polish(w,z0,85)
   if valid(z)[0]:found.append((r,z))
  checks=np.vstack([np.array([z for _,z in found]),pool[np.argsort((V@w)/den)[:20]],newvalley]);actual=np.column_stack([a(checks)for a in acts]);mixed=actual@w;dd=dist2(checks);order=np.argsort(mixed/np.maximum(dd,1e-8));rr['worst10']=[{'point':checks[j].tolist(),'R':float(mixed[j]),'components_R':actual[j].tolist(),'dist2':float(dd[j]),'Gram':float(gram(checks[j])[0])}for j in order[:10]];rr['elapsed_seconds']=time.monotonic()-START;save();print('round',iteration+1,rr,flush=True)
  bad=(mixed < -2e-12)&(dd>1e-8)
  if not np.any(bad):
   result['weights_proposal']={'weights':w.tolist(),'rational_weights':rr['rational_weights'],'eta_sample':float(eta),'A':[sum(w[j]*np.array(models[j]['A'][k])for j in range(3)).tolist()for k in range(11)],'c':float(sum(w[j]*models[j]['c']for j in range(3))),'source_models':models,'third_batch_common_N':data['third_batch_common_N'],'indices':data['indices'],'warning':'original float seeds only; corrected true-root endpoint family and H validation still needed'};result['stop_reason']='centered mixture passes finite contact annuli, curves, and valley polish';break
  pool=np.vstack([pool,checks[bad]]);V=np.vstack([V,actual[bad]])
except Budget as e:result['stop_reason']=str(e)
result.setdefault('stop_reason','finite rounds/budget exhausted');result['elapsed_seconds']=time.monotonic()-START;save();signal.alarm(0);print('done',result['stop_reason'],'seconds',result['elapsed_seconds'],'proposal',result['weights_proposal'] is not None,flush=True)
