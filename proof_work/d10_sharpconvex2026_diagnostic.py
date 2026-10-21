"""Finite three-existing-PSD-seed convex hull diagnosis, no SDP."""
import time,json,hashlib,ast,itertools,signal
from pathlib import Path
START=time.monotonic()
import numpy as np
from scipy.optimize import linprog,differential_evolution,NonlinearConstraint
from sharp_boundary_actualf_v3 import random_cond,boundary_points,valid,Compiled
from d12_contact2026_core import exact_candidate,RSTRING
from fractions import Fraction
from certify_three_point_d4 import const,add,scale,mul,mono,permute,diag
ROOT=Path(__file__).parent;OUT=ROOT/'d10_sharpconvex2026_results.json';assert not OUT.exists()
class Budget(Exception):pass
signal.signal(signal.SIGALRM,lambda *x:(_ for _ in ()).throw(Budget('60second hard budget')));signal.alarm(59)
source=ROOT/'sharp_contact_refinement2026_batch3_best_original_data.json';data=json.loads(source.read_text());models=[data['first_batch_original_PSD_seed'],*data['third_batch_original_models']];assert len(models)==3
assert all(s['min_B_eigenvalue']>9e-7 for s in models)
src=ROOT/'sharp_contact_refinement2026_refine.py';tree=ast.parse(src.read_text());node=next(n for n in tree.body if isinstance(n,ast.ClassDef)and n.name=='IndependentActual');ns={'np':np,'itertools':itertools,'DEGREE':10};exec(compile(ast.Module(body=[node],type_ignores=[]),str(src),'exec'),ns)
acts=[ns['IndependentActual']([np.array(a)for a in s['A']],s['c'])for s in models]
valley=json.loads((ROOT/'negative_valley_seed1_2026_summary.json').read_text());cand=np.array([[float(z)for z in p]for p in exact_candidate(Fraction(RSTRING))[0]])
known=np.array([q['center_minimum_sample']for q in valley['valleys'][:3]]+[[-.9655589354,-.4069479195,.5089797407],[-.9993574670,-.0179239136,-.0179239017],[.3727866847,.56,-.0401443734],[-.296937,.422535,.422535],[.56,.56,.56],[-1,0,0],[-1,-.56,.56]])
points=np.vstack([known,cand]);V=np.column_stack([a(points)for a in acts]);rows=[{'point':p.tolist(),'R':v.tolist(),'Gram':float(1+2*np.prod(p)-p@p),'valid':bool(valid(p)[0])}for p,v in zip(points,V)]
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
rng=np.random.default_rng(2026101728);random=random_cond(50000,rng);boundary=boundary_points(10000,rng);pool=np.vstack([points,random,boundary]);V=vals(pool);result['random_count']=50000;result['boundary_count']=10000;result['compiled_original_difference']=float(np.max(abs(vals(points)-np.column_stack([a(points)for a in acts]))));save()
def gram(p):p=np.atleast_2d(p);return 1+2*np.prod(p,axis=1)-np.sum(p*p,axis=1)
try:
 for iteration in range(3):
  lp=linprog([0,0,0,1],A_ub=np.column_stack([-V,-np.ones(len(V))]),b_ub=np.zeros(len(V)),A_eq=[[1,1,1,0]],b_eq=[1],bounds=[(.01,1),(0,1),(0,1),(0,None)],method='highs',options={'time_limit':8})
  row={'round':iteration+1,'linprog_success':bool(lp.success),'message':str(lp.message),'pool_count':len(pool)}
  if not lp.success:result['history'].append(row);result['stop_reason']='sample LP failed';break
  w=lp.x[:3];tau=float(lp.x[3]);row.update(weights=w.tolist(),sample_tau=tau,sample_min_R=float((V@w).min()))
  if tau>=1e-7:result['history'].append(row);result['stop_reason']='sample LP tau>=1e-7';break
  deadline=min(time.monotonic()+4.5,START+54);found=[];neval=0
  def decon(z):
   z=np.asarray(z);g=gram(z.reshape(3,-1).T);return float(g[0])if z.ndim==1 else g[None]
  def obj(z):
   global neval
   if time.monotonic()>deadline:raise Budget('DE finite deadline')
   z=np.asarray(z);p=z.reshape(3,-1).T;r=vals(p)@w;neval+=len(p)
   if len(r):q=int(r.argmin());found.append((float(r[q]),p[q].copy()))
   return float(r[0])if z.ndim==1 else r
  init=random_cond(72,rng);init[:12]=cand
  try:opt=differential_evolution(obj,[(-1,.56)]*3,constraints=[NonlinearConstraint(decon,0,np.inf)],init=init,maxiter=100000,polish=False,seed=20261017+iteration,vectorized=True,updating='deferred',tol=1e-10,callback=lambda x,convergence:time.monotonic()>deadline)
  except Budget:pass
  check=np.vstack([pool[np.argsort(V@w)[:40]],np.array([z[1]for z in sorted(found,key=lambda z:z[0])[:40]])]);actual=np.column_stack([a(check)for a in acts]);mix=actual@w;q=int(mix.argmin());row.update(independent_min_R=float(mix[q]),worst_point=check[q].tolist(),worst_components=actual[q].tolist(),DE_evaluations=neval,elapsed_seconds=time.monotonic()-START);result['history'].append(row);save()
  if max(actual[q])<-1e-8:result['common_negative_witness']={'point':check[q].tolist(),'R':actual[q].tolist()};result['stop_reason']='new common-negative witness';break
  if mix[q]>-1e-9:result['weights_proposal']={'weights':w.tolist(),'source_sha256':result['source_sha256'],'independent_min_R':float(mix[q]),'source_model_keys':result['model_keys']};result['stop_reason']='numerically plausible convex weights; exact root correction and validation remain';break
  more=check[np.argsort(mix)[:30]];pool=np.vstack([pool,more]);V=np.vstack([V,vals(more)])
 result.setdefault('stop_reason','three finite LP/DE rounds exhausted')
except Budget as e:result['stop_reason']=str(e)
result['elapsed_seconds']=time.monotonic()-START;save();signal.alarm(0);print(json.dumps(result),flush=True)
