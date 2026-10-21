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
ROOT=Path(__file__).parent;OUT=ROOT/'d10_sharpconvex2026_center_verification.json';assert not OUT.exists()
class Budget(Exception):pass
signal.signal(signal.SIGALRM,lambda *x:(_ for _ in ()).throw(Budget('60second hard budget')));signal.alarm(42)
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
rng=np.random.default_rng(2026101733);random=random_cond(100000,rng);boundary=boundary_points(10000,rng);pool=np.vstack([points,random,boundary]);V=vals(pool);result['random_count']=50000;result['boundary_count']=10000;result['compiled_original_difference']=float(np.max(abs(vals(points)-np.column_stack([a(points)for a in acts]))));save()
def gram(p):p=np.atleast_2d(p);return 1+2*np.prod(p,axis=1)-np.sum(p*p,axis=1)

proposal=json.loads((ROOT/'d10_sharpconvex2026_center_results.json').read_text())['weights_proposal'];w=np.array(proposal['weights']);contacts=np.unique(np.vstack([cand[:,pm]for pm in itertools.permutations(range(3))]),axis=0)
def dist2(p):return np.min(np.sum((np.atleast_2d(p)[:,None,:]-contacts[None,:,:])**2,axis=2),axis=1)
dd=dist2(pool);far=dd>=1e-6;rat=(V@w)/np.maximum(dd,1e-6);ix=np.flatnonzero(far);checklist=[pool[ix[np.argsort(rat[far])[:20]]]];found=[];deadline=time.monotonic()+7.5
# Second and final bounded DE run, on independently sampled pool and seed.
def constr(z):
 z=np.asarray(z);p=z.reshape(3,-1).T;g=gram(p);d=dist2(p)-1e-6;return np.array([g[0],d[0]])if z.ndim==1 else np.vstack([g,d])
def obj(z):
 if time.monotonic()>deadline:raise Budget('finite DE deadline')
 z=np.asarray(z);p=z.reshape(3,-1).T;r=(vals(p)@w)/np.maximum(dist2(p),1e-6)
 if len(r):j=int(r.argmin());found.append((float(r[j]),p[j].copy()))
 return float(r[0])if z.ndim==1 else r
try:de=differential_evolution(obj,[(-1,.56)]*3,constraints=[NonlinearConstraint(constr,[0,0],[np.inf,np.inf])],init=random_cond(90,rng),maxiter=100000,polish=False,seed=2026101733,vectorized=True,updating='deferred',callback=lambda x,convergence:time.monotonic()>deadline)
except Budget:pass
if found:checklist.append(np.array([z[1]for z in sorted(found,key=lambda z:z[0])[:30]]))
check=np.vstack(checklist);ddcheck=dist2(check);actual=np.column_stack([a(check)for a in acts]);R=actual@w;ratio=R/np.maximum(ddcheck,1e-6);order=np.argsort(ratio);rows=[{'point':check[i].tolist(),'R':float(R[i]),'R_components':actual[i].tolist(),'dist2':float(ddcheck[i]),'R_over_dist2':float(ratio[i]),'Gram':float(gram(check[i])[0])}for i in order[:10]if ddcheck[i]>=1e-6]
A=[np.array(a)for a in proposal['A']];N=[np.array(n).reshape(len(A[k]),-1)for k,n in enumerate(proposal['third_batch_common_N'])];Bs=[];reconstruction=[]
for a,n in zip(A,N):
 if n.shape[1]:pn=np.linalg.pinv(n);b=pn@a@pn.T;Bs.append((b+b.T)/2);reconstruction.append(float(np.max(abs(a-n@b@n.T))))
 else:reconstruction.append(float(np.max(abs(a))))
result={'warning':'NUMERICAL ONLY. Independent revalidation, no global minimum/positivity/Thomson claim. Near-contact domain remains for exact local analysis.','weights':w.tolist(),'rational_weights':proposal['rational_weights'],'source_sha256':proposal['source_sha256'],'center_model_file':str(ROOT/'d10_sharpconvex2026_center_results.json'),'independent_random_count':100000,'independent_boundary_count':10000,'independent_random_seed':2026101733,'sample_far_min_R_over_dist2':float(rat[far].min()),'independent_worst10_far_original_six_permutations':rows,'mixed_reduced_min_eigenvalue':min(float(np.linalg.eigvalsh(b).min())for b in Bs),'mixed_reduced_trace':sum(float(np.trace(b))for b in Bs),'mixed_A_common_N_B_reconstruction_max_error':max(reconstruction),'common_N_orthonormal_error':max(float(np.max(abs(n.T@n-np.eye(n.shape[1]))))for n in N if n.shape[1]),'candidate_min_R':float((np.column_stack([a(cand)for a in acts])@w).min()),'elapsed_seconds':time.monotonic()-START}
signal.alarm(0);OUT.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
