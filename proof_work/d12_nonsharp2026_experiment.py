"""Finite full-Gram degree12 nonsharp numerical experiment; no certificate claim."""
import time,json,hashlib,warnings
from pathlib import Path
START=time.monotonic()
import numpy as np
import cvxpy as cp
from scipy.optimize import minimize,differential_evolution,NonlinearConstraint
from d12_contact2026_core import exact_candidate,original,RSTRING
from sharp_boundary_actualf_v3 import polynomials,Compiled,random_cond,boundary_points,near_points,dedup,valid
from d12_contact2026_solver import IndependentActual,solver_info
from sharp_three_point import ENERGY
from three_point_sampled import design
from fractions import Fraction
ROOT=Path(__file__).parent
OUT=ROOT/'d12_nonsharp2026_results.json'
assert not OUT.exists()
class Budget(Exception):pass
rng=np.random.default_rng(2026101726)
snap=ROOT/'d12_competitive_probe2026_snapshot.json'
assert hashlib.sha256(snap.read_bytes()).hexdigest()=='70211e9762a6893f3cf2699f115c1d3bf3e8212b58870268ec89b6bd02f7434c'
data=json.loads(snap.read_text());warm=data['solution'];N=[np.asarray(n) for n in warm['N']]
P,indices=polynomials(N,12);comp=Compiled(P);assert len(indices)==322
cand=np.array([[float(v)for v in p]for p in exact_candidate(Fraction(RSTRING))[0]])
known=np.array([[-.6385403,-.5549004,.3503408],[-.9457081,-.6695418,.3918134],[-.7509654,-.1631469,.2695271]])
ref=np.array(warm['x'])
mandatory=dedup(np.vstack([known,cand,*[cand+rng.normal(0,s,(len(cand),3))for s in (1e-4,1e-3,.01)for _ in range(24)]]))
old=json.loads((ROOT/'nonsharp_nullspace_actualf_d10_run2.json').read_text())
pool=dedup(np.vstack([data['training_points'],old['training_points']]))
rank=np.argsort(comp.kernel(ref)(pool));initial=dedup(np.vstack([mandatory,pool[rank[:3500]],random_cond(900,rng),boundary_points(400,rng),near_points(200,rng)]))
# Select at most 6000, preserving candidate neighborhoods and all known negatives.
other=dedup(initial);budget=6000-len(mandatory)
points=dedup(np.vstack([mandatory,other[np.argsort(comp.kernel(ref)(other))[:budget]]]))
x=cp.Variable(len(indices));x.value=ref;t=cp.Variable(nonneg=True);tau=1e-6*t
lookup={q:j for j,q in enumerate(indices)}
B={k:cp.bmat([[x[lookup[k,min(i,j),max(i,j)]]for j in range(n.shape[1])]for i in range(n.shape[1])])for k,n in enumerate(N)if n.shape[1]}
tr=sum(cp.trace(v)for v in B.values());base=[v>>1e-8*np.eye(v.shape[0])for v in B.values()]+[tr<=500]
result={'warning':'NUMERICAL MODEL ONLY; no certificate, strict bound, or global minimum claim','degree':12,'unknowns':len(indices),'contact_equalities':0,'jet_constraints':0,'domain':'Gram PSD intersection [-1,.56]^3, no lowerdot/budget/Cpair restrictions','objective':'min tau+1e-8 trace (scaled by 1e6)','PSD_margin':1e-8,'trace_cap':500,'warmstart_sha256':hashlib.sha256(snap.read_bytes()).hexdigest(),'N':[n.tolist()for n in N],'indices':[list(q)for q in indices],'initial_training_points':points.tolist(),'settings':{'solver':'CLARABEL','time_limit':65.,'max_iter':300,'tol_feas':1e-10,'tol_gap_abs':1e-9,'tol_gap_rel':1e-9,'warm_start':True},'history':[]}
def save():OUT.write_text(json.dumps(result,indent=2)+'\n')
save();print('BUILD',len(points),'unknowns',len(indices),'seconds',time.monotonic()-START,flush=True)
for it in range(3):
 if time.monotonic()-START>212:result['stop_reason']='remaining total time insufficient for another solve and independent validation';break
 D=comp.design(points);rhs=np.sum((2-2*points)**(-.5),axis=1)-ENERGY/12
 prob=cp.Problem(cp.Minimize(t+.01*tr),base+[D@x<=rhs+tau]);tic=time.monotonic();err=None
 try:prob.solve(**result['settings'])
 except cp.error.SolverError as e:err=repr(e)
 row={'round':it+1,'training_count':len(points),'solver_error':err,'solve_seconds':time.monotonic()-tic,'solver_status':prob.status}
 if prob.solver_stats is not None:row['solver_info']=solver_info(prob)
 if x.value is None or tau.value is None:
  result['history'].append(row);result['stop_reason']='solver returned no iterate';save();break
 xx=np.array(x.value).ravel();tv=float(tau.value);bb,AA,c0=original(xx,N,indices);cc=c0-tv
 eig={k:np.linalg.eigvalsh(v).tolist()for k,v in bb.items()};mineig=min(min(v)for v in eig.values());trace=float(sum(np.trace(v)for v in bb.values()))
 actual=IndependentActual(AA,cc);raw=comp.kernel(xx)
 def residual(p,grad=False):
  if grad:
   v,g=raw(p,True);return v+tv,g
  return raw(p)+tv
 # Fresh independent random validation every round, including Gram boundary and antipodes.
 groups={'random':random_cond(12000,rng),'boundary_random':boundary_points(2500,rng),'near_antipodal':near_points(1500,rng),'candidate_and_known':np.vstack([cand,known])}
 vals={};found=[];add=[]
 for name,pp in groups.items():
  vv=np.concatenate([residual(pp[j:j+800])for j in range(0,len(pp),800)]);ii=np.argsort(vv);vals[name]={'count':len(pp),'min_R':float(vv[ii[0]]),'negative_count':int(np.sum(vv<0)),'worst_point':pp[ii[0]].tolist()};found.extend((float(vv[q]),pp[q].copy(),name)for q in ii[:30]);add.append(pp[ii[:350]])
 # Direct dot-coordinate SLSQP on the full Gram domain, using analytic compiled derivatives.
 def gram(z):return 1+2*np.prod(z)-z@z
 def gj(z):u,v,w=z;return np.array([2*(v*w-u),2*(u*w-v),2*(u*v-w)])
 local_deadline=time.monotonic()+6
 for _,seed,_ in sorted(found,key=lambda z:z[0])[:10]:
  if time.monotonic()>local_deadline:break
  def obj(z):
   if time.monotonic()>local_deadline:raise Budget()
   vv,gg=residual(z,True);return float(vv[0]),gg[0]
  try:
   opt=minimize(obj,seed,jac=True,method='SLSQP',bounds=[(-1,.56)]*3,constraints=[{'type':'ineq','fun':gram,'jac':gj}],options={'maxiter':100,'ftol':1e-13})
   if valid(opt.x)[0]:found.append((float(residual(opt.x)[0]),opt.x.copy(),'SLSQP'));add.append(opt.x[None])
  except Budget:break
 de_start=time.monotonic();de_deadline=de_start+12;de_evals=0
 def decon(z):
  z=np.asarray(z);p=z.reshape(3,-1).T;v=1+2*np.prod(p,axis=1)-np.sum(p*p,axis=1);return float(v[0])if z.ndim==1 else v[None]
 def deobj(z):
  global de_evals
  if time.monotonic()>de_deadline:raise Budget()
  z=np.asarray(z);pp=z.reshape(3,-1).T;vv=residual(pp);de_evals+=len(pp)
  if len(vv):
   q=int(vv.argmin());found.append((float(vv[q]),pp[q].copy(),'DE_evaluated'))
  return float(vv[0])if z.ndim==1 else vv
 init=random_cond(72,rng);init[:12]=cand
 try:
  de=differential_evolution(deobj,[(-1,.56)]*3,constraints=[NonlinearConstraint(decon,0,np.inf)],init=init,maxiter=100000,tol=1e-10,polish=False,vectorized=True,updating='deferred',seed=20261017+it,callback=lambda x,convergence:time.monotonic()>=de_deadline)
  de_status=str(de.message)
 except Budget:de_status='12 second budget'
 found=sorted((v,p,k)for v,p,k in found if valid(p)[0]) if False else sorted([z for z in found if valid(z[1])[0]],key=lambda z:z[0])
 # Validate actual original A on random checks AND all discovered low residual points.
 check=np.vstack([random_cond(80,rng),np.array([z[1]for z in found[:100]])]);av=actual(check);cv=residual(check);q=int(av.argmin());minR=float(av[q]);worst=check[q]
 origdesign=np.sum((2-2*check[:80])**(-.5),axis=1)-cc-sum(np.einsum('nij,ij->n',m,a)for m,a in zip(design(check[:80],12),AA))
 empirical=float(ENERGY-12*(tv-minR));trainR=rhs-D@xx+tv
 row.update({'tau':tv,'trace':trace,'min_B_eigenvalue':mineig,'block_eigenvalues':eig,'training_min_R':float(trainR.min()),'random_validation':vals,'DE_seconds':time.monotonic()-de_start,'DE_evaluations':de_evals,'DE_status':de_status,'independent_actual_min_R':minR,'worst_point':worst.tolist(),'worst_gram':float(gram(worst)),'actual_compiled_discrepancy':float(max(abs(av-cv))),'original_design_discrepancy':float(max(abs(origdesign-av[:80]))),'Bcandidate':float(ENERGY-12*tv),'empirical_corrected_bound':empirical,'seconds':time.monotonic()-START})
 model={'round':it+1,'A':[a.tolist()for a in AA],'B':{k:v.tolist()for k,v in bb.items()},'x':xx.tolist(),'N':[n.tolist()for n in N],'c':cc,'c0':c0,'tau':tv,'F111':float(AA[0].sum()),'min_B_eigenvalue':mineig,'trace':trace,'min_R_observed':minR,'worst_point':worst.tolist(),'empirical_corrected_bound':empirical,'cuts':points.tolist(),'indices':[list(q)for q in indices]}
 result['history'].append(row);result['solution']=model
 if 'best_solution'not in result or empirical>result['best_solution']['empirical_corrected_bound']:result['best_solution']=model
 result['training_points']=points.tolist();save();print('ROUND',json.dumps({k:v for k,v in row.items()if k not in ('block_eigenvalues','solver_info')}),flush=True)
 if empirical>25.75995 and mineig>=5e-9 and row['actual_compiled_discrepancy']<1e-9:
  result['stop_reason']='empirical threshold achieved with credible numerical PSD; export for exactification review';break
 if it>=1:
  prev=result['history'][-2]
  if abs(empirical-prev['empirical_corrected_bound'])<1e-7 or (empirical<prev['empirical_corrected_bound'] and abs(tv-prev['tau'])<1e-7):
   result['stop_reason']='two rounds show stagnation';break
 additions=dedup(np.vstack([*add,np.array([z[1]for z in found[:150]])]));aR=residual(additions);additions=additions[np.argsort(aR)[:500]]
 row['added_worst_cuts']=additions.tolist();row['added_random_violation_count']=int(sum(np.sum(residual(p)<0)for p in add[:4]));points=dedup(np.vstack([points,additions]));save()
result.setdefault('stop_reason','three round finite batch completed');result['elapsed_seconds']=time.monotonic()-START;save();print('FINAL',json.dumps({'stop_reason':result['stop_reason'],'elapsed_seconds':result['elapsed_seconds'],'best_empirical_corrected_bound':result.get('best_solution',{}).get('empirical_corrected_bound')}),flush=True)
