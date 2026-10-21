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
ROOT=Path(__file__).parent;OUT=ROOT/'d10_sharpconvex2026_center_results.json';assert not OUT.exists()
class Budget(Exception):pass
signal.signal(signal.SIGALRM,lambda *x:(_ for _ in ()).throw(Budget('60second hard budget')));signal.alarm(85)
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
rng=np.random.default_rng(2026101728);random=random_cond(100000,rng);boundary=boundary_points(10000,rng);pool=np.vstack([points,random,boundary]);V=vals(pool);result['random_count']=100000;result['boundary_count']=10000;result['compiled_original_difference']=float(np.max(abs(vals(points)-np.column_stack([a(points)for a in acts]))));save()
def gram(p):p=np.atleast_2d(p);return 1+2*np.prod(p,axis=1)-np.sum(p*p,axis=1)

contacts=np.unique(np.vstack([cand[:,pm]for pm in itertools.permutations(range(3))]),axis=0)
def dist2(p):
 p=np.atleast_2d(p);return np.min(np.sum((p[:,None,:]-contacts[None,:,:])**2,axis=2),axis=1)
result['candidate_permuted_count']=len(contacts)
result['history']=[];result['weights_proposal']=None
try:
 for iteration in range(2):
  d=dist2(pool);far=d>=1e-6;den=np.maximum(d,1e-6);Z=V/den[:,None]
  lp=linprog([0,0,0,-1],A_ub=np.column_stack([-Z,far.astype(float)]),b_ub=np.where(far,0,1e-12/den),A_eq=[[1,1,1,0]],b_eq=[1],bounds=[(.01,1),(0,1),(0,1),(None,None)],method='highs',options={'time_limit':12,'dual_feasibility_tolerance':1e-9,'primal_feasibility_tolerance':1e-9})
  row={'round':iteration+1,'linprog_success':bool(lp.success),'message':str(lp.message),'pool_count':len(pool)}
  if not lp.success:result['history'].append(row);result['stop_reason']='margin LP failed';break
  eta=float(lp.x[3]);w=lp.x[:3];ints=np.round(w*1000000).astype(int);ints[np.argmax(ints)]+=1000000-sum(ints);w=ints/1000000
  row.update(eta=eta,raw_weights=lp.x[:3].tolist(),weights=w.tolist(),rational_weights=[str(Fraction(int(z),1000000))for z in ints],sample_min_R=float((V@w).min()),sample_far_min_ratio=float(((V@w)[far]/d[far]).min()))
  if eta<=0:result['history'].append(row);result['stop_reason']='nonpositive sample normalized margin';break
  mixA=[sum(w[j]*np.array(models[j]['A'][k])for j in range(3))for k in range(11)];mixc=sum(w[j]*models[j]['c']for j in range(3));actmix=ns['IndependentActual'](mixA,mixc);found=[]
  def gj(z):u,v,t=z;return np.array([2*(v*t-u),2*(u*t-v),2*(u*v-t)])
  for seedpoint in known.tolist():
   def localobj(z):vv,g=actmix(z,True);return float(vv[0]),g[0]
   opt=minimize(localobj,seedpoint,jac=True,method='SLSQP',bounds=[(-1,.56)]*3,constraints=[{'type':'ineq','fun':lambda z:float(gram(z)[0]),'jac':gj}],options={'maxiter':70,'ftol':1e-14})
   if valid(opt.x)[0]:found.append((float(actmix(opt.x)[0])/max(float(dist2(opt.x)[0]),1e-6),opt.x.copy()))
  deadline=min(time.monotonic()+7.5,START+77);neval=0
  def decon(z):
   z=np.asarray(z);p=z.reshape(3,-1).T;g=gram(p);dd=dist2(p)-1e-6;return np.array([g[0],dd[0]])if z.ndim==1 else np.vstack([g,dd])
  def obj(z):
   global neval
   if time.monotonic()>deadline:raise Budget('DE finite deadline')
   z=np.asarray(z);p=z.reshape(3,-1).T;r=(vals(p)@w)/np.maximum(dist2(p),1e-6);neval+=len(p)
   if len(r):q=int(r.argmin());found.append((float(r[q]),p[q].copy()))
   return float(r[0])if z.ndim==1 else r
  init=random_cond(90,rng)
  try:opt=differential_evolution(obj,[(-1,.56)]*3,constraints=[NonlinearConstraint(decon,[0,0],[np.inf,np.inf])],init=init,maxiter=100000,polish=False,seed=2026101731+iteration,vectorized=True,updating='deferred',tol=1e-10,callback=lambda x,convergence:time.monotonic()>deadline)
  except Budget:pass
  faridx=np.flatnonzero(far);worstpool=faridx[np.argsort((V@w)[far]/d[far])[:20]];check=np.vstack([pool[worstpool],np.array([z[1]for z in sorted(found,key=lambda z:z[0])[:40]]),cand]);actual=np.column_stack([a(check)for a in acts]);mixed=actual@w;dd=dist2(check);ratio=mixed/np.maximum(dd,1e-6);order=np.argsort(ratio);q=int(order[0]);worst10=[{'point':check[i].tolist(),'R':float(mixed[i]),'components_R':actual[i].tolist(),'dist2':float(dd[i]),'ratio':float(ratio[i]),'Gram':float(gram(check[i])[0])}for i in order[:10]]
  row.update(independent_min_R=float(mixed.min()),independent_min_normalized_R=float(ratio[q]),worst10=worst10,DE_evaluations=neval,elapsed_seconds=time.monotonic()-START);result['history'].append(row);save()
  common=[i for i in range(len(check))if max(actual[i])<-1e-8]
  if common:result['common_negative_witness']=worst10[0];result['stop_reason']='common-negative point';break
  bad=(mixed<-1e-9)&(dd>=1e-6)
  if not np.any(bad):
   result['weights_proposal']={'weights':w.tolist(),'rational_weights':row['rational_weights'],'source_sha256':result['source_sha256'],'source_model_keys':result['model_keys'],'eta_sample_LP':eta,'observed_min_normalized_R':float(ratio[q]),'independent_min_R':float(mixed.min()),'A':mixA,'c':mixc,'source_models':models,'third_batch_common_N':data['third_batch_common_N'],'indices':data['indices'],'contact_geometry_RSTRING':RSTRING,'warning':'original double A/c mixture only; true-root exact contact correction, PSD verification, local-zero proof, outside positivity remain'}
   result['stop_reason']='positive normalized numerical margin and no independent significant negative observed';break
  more=check[bad];pool=np.vstack([pool,more]);V=np.vstack([V,actual[bad]])
 result.setdefault('stop_reason','two centered LP/DE rounds exhausted')
except Budget as e:result['stop_reason']=str(e)
result['elapsed_seconds']=time.monotonic()-START
# ndarray matrices are intentionally exported as complete double data.
if result['weights_proposal'] is not None:
 result['weights_proposal']['A']=[a.tolist()for a in result['weights_proposal']['A']]
save();signal.alarm(0);print(json.dumps({k:v for k,v in result.items()if k not in ['weights_proposal','fixed_point_table']})+'\nproposal_exported='+str(result['weights_proposal']is not None),flush=True)
