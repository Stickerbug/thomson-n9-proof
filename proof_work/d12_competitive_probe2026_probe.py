#!/usr/bin/env python3
"""One <=89 second independent original-A competitive probe; discovery only."""
from pathlib import Path
from fractions import Fraction as F
import ast,itertools,json,time,hashlib
import numpy as np
from scipy.optimize import minimize,differential_evolution,NonlinearConstraint
BASE=Path(__file__).resolve().parent;P='d12_competitive_probe2026_'
class TimeBudget(Exception):pass
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
class OldResidual:
 def __init__(self,model,budget):
  self.terms=[(tuple(e),F(c))for e,c in model['residual_monomial']];self.e=np.array([e for e,c in self.terms],dtype=int);self.c=np.array([float(c)for e,c in self.terms]);self.maxp=int(self.e.max());self.budget=budget
 def __call__(self,points,gradient=False):
  p=np.atleast_2d(points);out=[];gg=[]
  for start in range(0,len(p),1024):
   z=p[start:start+1024];pw=[]
   for j in range(3):
    a=np.ones((len(z),self.maxp+1))
    for k in range(1,self.maxp+1):a[:,k]=a[:,k-1]*z[:,j]
    pw.append(a)
   mon=pw[0][:,self.e[:,0]]*pw[1][:,self.e[:,1]]*pw[2][:,self.e[:,2]];out.append(mon@self.c)
   if gradient:
    gg.append(np.column_stack([(pw[0][:,np.maximum(0,self.e[:,0]-(j==0))]*pw[1][:,np.maximum(0,self.e[:,1]-(j==1))]*pw[2][:,np.maximum(0,self.e[:,2]-(j==2))])@(self.c*self.e[:,j])for j in range(3)]))
  v=np.concatenate(out);return(v,np.vstack(gg))if gradient else v
 def exact(self,point):
  z=[F(str(x))for x in point];pw=[[x**k for k in range(self.maxp+1)]for x in z];return sum(c*pw[0][e[0]]*pw[1][e[1]]*pw[2][e[2]]for e,c in self.terms)
def gram(p):p=np.atleast_2d(p);return 1+2*np.prod(p,axis=1)-np.sum(p*p,axis=1)
def run():
 start=time.monotonic();deadline=start+88;outpath=BASE/(P+'results.json');assert not outpath.exists();data=json.loads((BASE/(P+'snapshot.json')).read_text());meta=json.loads((BASE/(P+'snapshot_metadata.json')).read_text());assert sha(BASE/(P+'snapshot.json'))==meta['sha256'];sol=data['solution'];assert sol['iteration']==meta['selected_iteration']
 sourcepath=BASE/'d12_contact2026_solver.py';source=sourcepath.read_text();tree=ast.parse(source);node=next(n for n in tree.body if isinstance(n,ast.ClassDef)and n.name=='IndependentActual');namespace={'np':np,'itertools':itertools,'DEGREE':12};exec(compile(ast.Module(body=[node],type_ignores=[]),str(sourcepath),'exec'),namespace);actual=namespace['IndependentActual']([np.array(a)for a in sol['A']],float(sol['c']))
 oldpath=BASE/'nonsharp_d10_root25_7599205_v10.json';oldmodel=json.loads(oldpath.read_text());upperpath=BASE/'pair056_optimized_certificate.json';upper=json.loads(upperpath.read_text());budget=7*(F(upper['U'])-F(oldmodel['target']));old=OldResidual(oldmodel,budget);bf=float(budget);rng=np.random.default_rng(2026101712)
 result={'warning':'DISCOVERY ONLY; no global/domain-minimum/Thomson-counterexample claim. The exact old-budget signs certify only exclusion of the specified finite-decimal triples, conditional on saved existing budget lemma.','snapshot':meta,'selected_iteration':sol['iteration'],'new_model':{'A':sol['A'],'c':sol['c'],'trace':sol.get('trace'),'min_B_eigenvalue':sol.get('min_B_eigenvalue')},'domain':'Gram>=0, all dots in[-1,.56], R_old_h27<=7(U-B); no old separable C constraint','budget_exact':str(budget),'budget_float':bf,'original_A_evaluator_source':ast.get_source_segment(source,node),'points':[],'search':{},'dependencies':{str(p):sha(p)for p in [sourcepath,oldpath,upperpath,BASE/'sharp_contact_refinement2026_kernel_budget_certificate.json',BASE/(P+'snapshot.json'),Path(__file__)]}}
 def describe(name,p,exact=False):
  z=np.asarray(p,dtype=float);rv=float(actual(z)[0]);ov=float(old(z)[0]);g=float(gram(z)[0]);row={'name':name,'point':z.tolist(),'R_new_actual':rv,'R_old_float':ov,'budget_minus_Rold_float':bf-ov,'Gram':g,'numeric_eligible':bool(g>=0 and z.min()>=-1 and z.max()<=.56 and ov<=bf)}
  if exact:
   v=old.exact(z);delta=v-budget;zz=[F(str(x))for x in z];gg=1+2*np.prod(zz)-sum(x*x for x in zz);row.update(R_old_exact=str(v),R_old_minus_budget_exact=str(delta),R_old_minus_budget_exact_sign=int(delta>0)-int(delta<0),Gram_exact=str(gg),fixed_decimal_point_strictly_budget_excluded=bool(delta>0))
  return row
 for h in data['history']:
  if 'worst_point'in h:result['points'].append(describe('fullworst_from_iteration'+str(h['iteration']),h['worst_point']['triangle'],True))
 result['points'].append(describe('final_fullworst_strict_inside',[-.980273235792661,.0993119914433429,.09931199744825939],True))
 valley=json.loads((BASE/'negative_valley_seed1_2026_summary.json').read_text());seeds=[np.array(v['center_minimum_sample'])for v in valley['valleys'][:3]]
 for i,p in enumerate(seeds):result['points'].append(describe('seed1_valley_T'+str(i+1),p,True))
 r=F(data['r_approximation']);a=1-F(3,2)*r*r;b=2*r*r-1;c=r*r/2-1
 def dot(i,j):
  if i>=6 and j>=6:return F(-1,2)
  if i>=6:i,j=j,i
  if j>=6:return-r if(j-6-i%3)%3==1 else r/2
  return a if i//3==j//3 else b if i%3==j%3 else c
 cand=np.array(sorted(set(tuple(sorted([float(dot(i,j)),float(dot(i,k)),float(dot(j,k))]))for i,j,k in itertools.combinations(range(9),3))))
 result['candidate_points']=[describe('candidate_'+str(i),p)for i,p in enumerate(cand)]
 print('POINTS',json.dumps([{k:v for k,v in r.items()if not k.endswith('_exact')}for r in result['points']]),flush=True)
 eligible=[];drawn=0
 while sum(map(len,eligible))<2500 and time.monotonic()<deadline-25:
  u,v=rng.uniform(-1,.56,(2,8000));t=u*v+np.sqrt(np.maximum(0,(1-u*u)*(1-v*v)))*np.cos(rng.uniform(0,np.pi,8000));pp=np.sort(np.column_stack([u,v,t]),axis=1);pp=pp[(pp.min(axis=1)>=-1)&(pp.max(axis=1)<=.56)&(gram(pp)>=0)];drawn+=8000;vv=old(pp);eligible.append(pp[vv<=bf])
 pool=np.vstack(eligible)if eligible else np.empty((0,3));pool=pool[:4000];rr=actual(pool)if len(pool)else np.empty(0);result['search']['random']={'drawn':drawn,'eligible_evaluated':len(pool),'minimum_R_new':None if not len(rr)else float(rr.min()),'worst_point':None if not len(rr)else pool[int(rr.argmin())].tolist()}
 candidates=[]
 def record(z,kind):
  z=np.sort(np.asarray(z));g=float(gram(z)[0]);ov=float(old(z)[0]);rv=float(actual(z)[0]);row={'kind':kind,'point':z.tolist(),'R_new_actual':rv,'Gram':g,'budget_minus_Rold':bf-ov,'strict_numeric_eligible':bool(g>=0 and ov<=bf and z.min()>=-1 and z.max()<=.56)};candidates.append(row);return row
 if len(rr):record(pool[int(rr.argmin())],'random')
 for p in seeds:record(p,'known_seed')
 local_rows=[];local_deadline=min(start+55,deadline-22);local_seeds=seeds+[p for p in cand]+[np.clip(p+rng.normal(0,.001,3),-1,.56)for p in cand]
 def gfun(z):return float(gram(z)[0])
 def gjac(z):u,v,t=z;return np.array([2*(v*t-u),2*(u*t-v),2*(u*v-t)])
 def kfun(z):return float((bf-old(z)[0])/bf)
 def kjac(z):return-old(z,True)[1][0]/bf
 for seed in local_seeds:
  if time.monotonic()>=local_deadline:break
  def fun(z):
   if time.monotonic()>=local_deadline:raise TimeBudget()
   v,g=actual(z,True);return float(v[0]*1000),g[0]*1000
  try:
   opt=minimize(fun,seed,jac=True,method='SLSQP',bounds=[(-1,.56)]*3,constraints=[{'type':'ineq','fun':gfun,'jac':gjac},{'type':'ineq','fun':kfun,'jac':kjac}],options={'maxiter':100,'ftol':1e-12});row=record(opt.x,'SLSQP');row.update(success=bool(opt.success),message=str(opt.message),iterations=int(opt.nit));local_rows.append(row)
  except TimeBudget:break
 result['search']['SLSQP']=local_rows
 de_start=time.monotonic();de_deadline=min(de_start+20,deadline-2);de_best=[];de_evaluations=0
 def decon(x):
  p=np.asarray(x);pp=p.reshape(3,-1).T;v=np.vstack([gram(pp),(bf-old(pp))/bf]);return v[:,0]if p.ndim==1 else v
 def defun(x):
  nonlocal de_evaluations
  if time.monotonic()>=de_deadline:raise TimeBudget()
  p=np.asarray(x);pp=p.reshape(3,-1).T;v=actual(pp);de_evaluations+=len(pp)
  if len(v):de_best.append((float(v.min()),pp[int(v.argmin())].copy()))
  return float(v[0])if p.ndim==1 else v
 de_status='skipped_time_or_insufficient_pool'
 if len(pool)>=54 and time.monotonic()<de_deadline:
  initial=pool[rng.choice(len(pool),54,replace=False)].copy()
  for j,p in enumerate(seeds):initial[j]=p
  try:
   opt=differential_evolution(defun,[(-1,.56)]*3,constraints=[NonlinearConstraint(decon,[0,0],[np.inf,np.inf])],init=initial,maxiter=100000,tol=1e-10,polish=False,vectorized=True,updating='deferred',seed=20261017,callback=lambda x,convergence:time.monotonic()>=de_deadline);record(opt.x,'DE_result');de_status=str(opt.message)
  except TimeBudget:de_status='20second_or_remaining_budget_guard'
 if de_best:record(min(de_best,key=lambda a:a[0])[1],'DE_best_evaluated')
 result['search']['DE']={'seconds':time.monotonic()-de_start,'requested_seconds':20,'status':de_status,'objective_point_evaluations':de_evaluations}
 strict=[r for r in candidates if r['strict_numeric_eligible']];best=min(strict,key=lambda r:r['R_new_actual'])if strict else None
 result['search']['candidate_results']=candidates;result['best_strict_numeric_eligible']=best
 if best is not None:result['best_point_exact_old_budget_check']=describe('best_discovered',best['point'],True)
 result['elapsed_seconds']=time.monotonic()-start;result['numerical_seconds_budget']=90;result['at_least_2000_random_eligible_completed']=len(pool)>=2000;result['domain_minimum_claimed']=False
 outpath.write_text(json.dumps(result,indent=2)+'\n');print('FINAL',json.dumps({'elapsed_seconds':result['elapsed_seconds'],'random':result['search']['random'],'SLSQP_count':len(local_rows),'DE':result['search']['DE'],'best':best}),flush=True)
 return result
if __name__=='__main__':run()
