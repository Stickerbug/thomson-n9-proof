#!/usr/bin/env python3
"""One 45-second probe of a necessary GLOBAL-MINIMIZER domain; no SDP."""
from pathlib import Path
from fractions import Fraction as F
import ast,itertools,json,time,hashlib
import numpy as np
import mpmath as mp
from scipy.optimize import minimize,differential_evolution,NonlinearConstraint
from d12_competitive_probe2026_probe import OldResidual,gram
BASE=Path(__file__).resolve().parent;P='d12_minimizer_domain2026_';LOW=F(-9957,10000);HIGH=F(14,25)
class TimeBudget(Exception):pass
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def extract(path,name,kind,namespace):
 text=path.read_text();node=next(n for n in ast.parse(text).body if isinstance(n,kind)and n.name==name);exec(compile(ast.Module(body=[node],type_ignores=[]),str(path),'exec'),namespace);return ast.get_source_segment(text,node)
def run():
 start=time.monotonic();deadline=start+43;outpath=BASE/(P+'results.json');assert not outpath.exists()
 snap=BASE/'d12_competitive_probe2026_snapshot.json';metapath=BASE/'d12_competitive_probe2026_snapshot_metadata.json';meta=json.loads(metapath.read_text());assert sha(snap)==meta['sha256']=='70211e9762a6893f3cf2699f115c1d3bf3e8212b58870268ec89b6bd02f7434c';data=json.loads(snap.read_text());sol=data['solution'];assert sol['iteration']==meta['selected_iteration']==2
 solver=BASE/'d12_contact2026_solver.py';ns={'np':np,'itertools':itertools,'DEGREE':12};actual_source=extract(solver,'IndependentActual',ast.ClassDef,ns);actual=ns['IndependentActual']([np.array(a)for a in sol['A']],float(sol['c']))
 op=BASE/'nonsharp_d10_root25_7599205_v10.json';rp=BASE/'nonsharp_d10_root25_7599205_v10_result.json';upp=BASE/'pair056_optimized_certificate.json';model=json.loads(op.read_text());report=json.loads(rp.read_text());assert report['status']=='certified'and report['pending']==0 and report['model_sha256']==sha(op);upper=json.loads(upp.read_text());budget=7*(F(upper['U'])-F(model['target']));bf=float(budget);old=OldResidual(model,budget);lo=float(LOW);hi=float(HIGH);rng=np.random.default_rng(2026101727)
 priorpath=BASE/'d12_competitive_probe2026_results.json';prior=json.loads(priorpath.read_text());assert prior['snapshot']['sha256']==meta['sha256'];seeds=[np.array(r['point'])for r in prior['points']if r['name'].startswith('seed1_valley')];cand=np.array([r['point']for r in prior['candidate_points']]);rows=[];best_evaluated=None
 def record(p,kind):
  nonlocal best_evaluated
  p=np.sort(np.array(p,dtype=float));rv=float(actual(p)[0]);g=float(gram(p)[0]);k=bf-float(old(p)[0]);row={'kind':kind,'point':p.tolist(),'R_new_actual':rv,'Gram':g,'budget_minus_Rold':k,'numeric_eligible':bool(g>=0 and k>=0 and p.min()>=lo and p.max()<=hi)};rows.append(row)
  if row['numeric_eligible']and(best_evaluated is None or rv<best_evaluated['R_new_actual']):best_evaluated=row
  return row
 excluded_previous=[]
 for r in prior['search']['candidate_results']:
  if r['kind']in ['random','DE_result']:
   p=[F(str(x))for x in r['point']];excluded_previous.append({'kind':r['kind'],'point':r['point'],'below_new_dot_lower_bound_exact':min(p)<LOW,'min_dot_minus_lower_exact':str(min(p)-LOW)})
 known=[record(p,'T'+str(i+1))for i,p in enumerate(seeds)];contact_values=actual(cand)
 poolparts=[];drawn=0
 while sum(map(len,poolparts))<1300 and time.monotonic()<start+9:
  u,v=rng.uniform(lo,hi,(2,6000));t=u*v+np.sqrt(np.maximum(0,(1-u*u)*(1-v*v)))*np.cos(rng.uniform(0,np.pi,6000));p=np.sort(np.column_stack([u,v,t]),axis=1);p=p[(p.min(axis=1)>=lo)&(p.max(axis=1)<=hi)&(gram(p)>=0)];ov=old(p);poolparts.append(p[ov<=bf]);drawn+=6000
 pool=np.vstack(poolparts)if poolparts else np.empty((0,3));pool=pool[:2000];rv=actual(pool)if len(pool)else np.empty(0);idx=np.argsort(rv);random={'drawn':drawn,'eligible_evaluated':len(pool),'minimum_R_new':float(rv.min())if len(rv)else None,'worst_point':pool[idx[0]].tolist()if len(rv)else None,'negative_below_minus_1e7_count':int(np.sum(rv< -1e-7))};random_rows=[record(pool[i],'random_low')for i in idx[:3]]
 local_seeds=[('T'+str(i+1),p)for i,p in enumerate(seeds)]+[('candidate_neighbor_'+str(i),np.clip(cand[i]+rng.normal(0,1e-4,3),lo,hi))for i in [0,len(cand)-1]]+[('random_low_'+str(j),pool[i])for j,i in enumerate(idx[:3])];assert len(local_seeds)<=8;local=[];last_eval=None
 def gfun(p):return float(gram(p)[0])
 def gjac(p):u,v,t=p;return np.array([2*(v*t-u),2*(u*t-v),2*(u*v-t)])
 def kfun(p):return (bf-float(old(p)[0]))/bf
 def kjac(p):return-old(p,True)[1][0]/bf
 for name,seed in local_seeds:
  if time.monotonic()>=start+26:break
  case_start=time.monotonic();local_end=min(case_start+2.4,start+26);last_eval=None
  def fun(p):
   nonlocal last_eval
   if time.monotonic()>=local_end:raise TimeBudget()
   value,gradient=actual(p,True);last_eval=np.array(p);return float(value[0]*1000),gradient[0]*1000
  try:
   opt=minimize(fun,seed,jac=True,method='SLSQP',bounds=[(lo,hi)]*3,constraints=[{'type':'ineq','fun':gfun,'jac':gjac},{'type':'ineq','fun':kfun,'jac':kjac}],options={'maxiter':65,'ftol':1e-12});row=record(opt.x,'SLSQP_result');status={'success':bool(opt.success),'message':str(opt.message),'iterations':int(opt.nit),'result':row}
  except TimeBudget:
   status={'success':False,'message':'per-start or shared SLSQP time limit','result':record(last_eval,'SLSQP_last_evaluation')if last_eval is not None else None}
  local.append({'seed_kind':name,'seed':np.array(seed).tolist(),'seconds':time.monotonic()-case_start,**status})
 de_start=time.monotonic();de_end=min(de_start+12,deadline-4);best_de=[];evaluations=0
 def constraint(p):
  if time.monotonic()>=de_end:raise TimeBudget()
  p=np.asarray(p);pp=p.reshape(3,-1).T;v=np.vstack([gram(pp),(bf-old(pp))/bf]);return v[:,0]if p.ndim==1 else v
 def objective(p):
  nonlocal evaluations
  if time.monotonic()>=de_end:raise TimeBudget()
  p=np.asarray(p);pp=p.reshape(3,-1).T;v=actual(pp);evaluations+=len(pp)
  if len(v):best_de.append((float(v.min()),pp[int(v.argmin())].copy()))
  return float(v[0])if p.ndim==1 else v
 de_status='not_started_insufficient_eligible'
 if len(pool)>=48 and time.monotonic()<de_end:
  initial=pool[rng.choice(len(pool),48,replace=False)].copy();initial[:3]=seeds
  for j,r in enumerate(random_rows):initial[3+j]=r['point']
  try:
   opt=differential_evolution(objective,[(lo,hi)]*3,constraints=[NonlinearConstraint(constraint,[0,0],[np.inf,np.inf])],init=initial,maxiter=100000,tol=1e-10,polish=False,vectorized=True,updating='deferred',seed=2026101727,callback=lambda x,convergence:time.monotonic()>=de_end);record(opt.x,'DE_result');de_status=str(opt.message)
  except TimeBudget:de_status='12second_or_shared_deadline'
 if best_de:record(min(best_de,key=lambda a:a[0])[1],'DE_best_evaluated')
 de={'seconds':time.monotonic()-de_start,'seconds_limit':12,'status':de_status,'objective_point_evaluations':evaluations}
 verifier=BASE/'sharp_contact_refinement2026_export.py';mp.mp.dps=80;mpns={'mp':mp,'itertools':itertools};extract(verifier,'mpR',ast.FunctionDef,mpns);verified=[]
 check=[]
 if random_rows:check.append(random_rows[0])
 if best_evaluated and(not check or best_evaluated['point']!=check[0]['point']):check.append(best_evaluated)
 for r in check:
  if time.monotonic()>=deadline-1:break
  p=r['point'];z=[F(str(x))for x in p];v=old.exact(p);g=1+2*z[0]*z[1]*z[2]-sum(x*x for x in z);k=budget-v
  verified.append({'point':p,'kind':r['kind'],'R_old_exact':str(v),'Gram_exact':str(g),'Gram_decimal':float(g),'budget_minus_Rold_exact':str(k),'budget_minus_Rold_decimal':float(k),'dot_lower_margin_exact':str(min(z)-LOW),'dot_upper_margin_exact':str(HIGH-max(z)),'exact_necessary_domain':bool(g>=0 and k>=0 and all(LOW<=x<=HIGH for x in z)),'new_actualf_80digit':mpns['mpR'](sol['A'],sol['c'],p)})
 result={'warning':'NUMERICAL DISCOVERY ONLY. New dot lower bound is supplied for GLOBAL MINIMIZERS, not arbitrary E<=U configurations. No domain-minimum/nonnegative/Thomson-counterexample claim.','previous_job_857':'completed exit0 and collected before this separate bounded task; not repeated','model_snapshot':meta,'iteration':2,'dot_lower_exact':str(LOW),'dot_upper_exact':str(HIGH),'budget_exact':str(budget),'domain':'Gram>=0; each dot in[-.9957,.56]; R_old_h27<=7(U-B). Additional dot lower bound accepted as parent-supplied necessary global-minimizer condition; not proved here.','original_A_evaluator_source':actual_source,'excluded_previous_negative_points':excluded_previous,'known_valley_points':known,'candidate_max_abs_R_new':float(np.max(np.abs(contact_values))),'random':random,'SLSQP':local,'DE':de,'all_recorded_points':rows,'best_numeric_eligible':best_evaluated,'fixed_point_verification':verified,'elapsed_seconds':time.monotonic()-start,'seconds_budget':45,'random_1000eligible_completed':len(pool)>=1000,'eight_SLSQP_starts_attempted':len(local)==8,'domain_nonnegativity_claimed':False,'domain_minimum_claimed':False,'dependencies':{str(p):sha(p)for p in [snap,metapath,solver,op,rp,upp,priorpath,verifier,BASE/'d12_competitive_probe2026_probe.py',Path(__file__)]}}
 assert result['elapsed_seconds']<45
 outpath.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k]for k in ['elapsed_seconds','random','DE','best_numeric_eligible','random_1000eligible_completed','eight_SLSQP_starts_attempted','candidate_max_abs_R_new']},indent=2),flush=True);return result
if __name__=='__main__':run()
