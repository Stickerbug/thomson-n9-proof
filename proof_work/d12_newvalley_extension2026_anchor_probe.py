#!/usr/bin/env python3
"""One bounded numerical one-external-point field probe; no SDP or packing."""
from pathlib import Path
from fractions import Fraction as F
import json,time,hashlib,itertools
import numpy as np
from scipy.optimize import minimize,differential_evolution,NonlinearConstraint
from dyadic_interval import I,S,BITS
BASE=Path(__file__).resolve().parent;P='d12_newvalley_extension2026_anchor_';LOW=F(-9957,10000);HIGH=F(14,25)
class TimeBudget(Exception):pass
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def qs(x):
 x=np.asarray(x);a,b=x[...,0],x[...,1];return np.stack([np.sin(a)*np.cos(b),np.sin(a)*np.sin(b),np.cos(a)],axis=-1)
def angles(q):return np.array([np.arccos(np.clip(q[2],-1,1)),np.arctan2(q[1],q[0])%(2*np.pi)])
def run():
 start=time.monotonic();prior=json.loads((BASE/'d12_newvalley_extension2026_results.json').read_text());prior_seconds=prior['elapsed_seconds'];deadline=start+55;outpath=BASE/(P+'results.json');assert not outpath.exists();coords=['-.9457080898901464','-.6695418187936286','.39181335775890314'];u,v,t=map(F,coords);gram=1+2*u*v*t-u*u-v*v-t*t;assert gram>0;s=np.sqrt(float(1-u*u));A=np.array([[1.,0,0],[float(u),s,0],[float(v),float(t-u*v)/s,np.sqrt(float(gram))/s]]);edgepairs=[(0,1),(0,2),(1,2)];edgevalues=[u,v,t]
 mp=BASE/'nonsharp_d10_root25_7599205_v10.json';rp=BASE/'nonsharp_d10_root25_7599205_v10_result.json';up=BASE/'pair056_optimized_certificate.json';model=json.loads(mp.read_text());report=json.loads(rp.read_text());assert report['status']=='certified'and report['pending']==0 and report['model_sha256']==sha(mp);upper=json.loads(up.read_text());terms=[(tuple(e),F(c))for e,c in model['residual_monomial']];rtriangle=sum(c*u**i*v**j*t**k for(i,j,k),c in terms);totalbudget=7*(F(upper['U'])-F(model['target']));K=totalbudget-rtriangle;threshold=K/6;assert K>0
 coefficients=[];gradient_coeff=[]
 for edge in edgevalues:
  C=np.zeros((28,28),dtype=np.longdouble);ee=np.longdouble(edge.numerator)/np.longdouble(edge.denominator)
  for(i,j,k),c in terms:C[j,k]+=np.longdouble(c.numerator)/np.longdouble(c.denominator)*ee**i
  coefficients.append(C);gradient_coeff.append((C[1:,:]*np.arange(1,28,dtype=np.longdouble)[:,None],C[:,1:]*np.arange(1,28,dtype=np.longdouble)[None,:]))
 def field(q,gradient=False):
  q=np.asarray(q);d=np.asarray(q,dtype=np.longdouble)@np.asarray(A.T,dtype=np.longdouble);values=[];grad=np.zeros(q.shape,dtype=np.longdouble)
  for(a,b),C,(Cx,Cy)in zip(edgepairs,coefficients,gradient_coeff):
   values.append(np.polynomial.polynomial.polyval2d(d[...,a],d[...,b],C))
   if gradient:
    gx=np.polynomial.polynomial.polyval2d(d[...,a],d[...,b],Cx);gy=np.polynomial.polynomial.polyval2d(d[...,a],d[...,b],Cy);grad+=gx[...,None]*A[a]+gy[...,None]*A[b]
  terms3=np.stack(values,axis=-1);phi=np.sum(terms3,axis=-1);return(phi,terms3,grad)if gradient else(phi,terms3)
 rows=[];best=None
 def record(q,kind):
  nonlocal best
  q=np.asarray(q,dtype=float);q=q/np.linalg.norm(q);d=q@A.T;value,three=field(q);phi=float(value);slack=min(float(d.min()-float(LOW)),float(float(HIGH)-d.max()));oldslack=float(K)-float(np.max(three));phislack=float(K)-phi;row={'kind':kind,'q':q.tolist(),'phi':phi,'phi_minus_K_over6':phi-float(threshold),'three_R_values':np.asarray(three,dtype=float).tolist(),'anchor_dots':d.tolist(),'anchor_dot_margin':slack,'individual_old_R_budget_margin':oldslack,'phi_budget_margin':phislack,'numeric_eligible':bool(slack>=0 and np.min(three)>=-1e-12),'q_norm_error':float(q@q-1)};rows.append(row)
  if row['numeric_eligible']and(best is None or phi<best['phi']):best=row
  return row
 n=10000;z=1-2*(np.arange(n)+.5)/n;az=np.arange(n)*np.pi*(3-np.sqrt(5));rad=np.sqrt(1-z*z);grid=np.column_stack([rad*np.cos(az),rad*np.sin(az),z]);d=grid@A.T;allowed=np.all((d>=float(LOW))&(d<=float(HIGH)),axis=1);grid=grid[allowed];vals,three=field(grid);budgetok=(np.max(three,axis=1)<=float(K))&(vals<=float(K))&(np.min(three,axis=1)>=-1e-12);allidx=np.argsort(vals);eligible_grid=grid;ev=vals;eid=np.argsort(ev)
 mesh={'total_sphere_points':n,'allowed_anchor_points':len(grid),'old_residual_budget_pass_count':int(np.sum(budgetok)),'anchor_only_search_points':len(eligible_grid),'minimum_phi_anchor_only':float(vals.min())if len(vals)else None,'minimum_phi_eligible':float(ev.min())if len(ev)else None,'below_K_over6_count':int(np.sum(ev<float(threshold))),'seconds':time.monotonic()-start}
 if len(eid):record(eligible_grid[eid[0]],'mesh_best')
 starts=[]
 # Retain separated low values first, then fill until eight starts.
 for k in eid:
  q=eligible_grid[k]
  if all(q@r<.99 for r in starts):starts.append(q)
  if len(starts)==8:break
 for k in eid:
  if len(starts)==8:break
  if not any(np.allclose(eligible_grid[k],q,rtol=0,atol=1e-14)for q in starts):starts.append(eligible_grid[k])
 local=[]
 def cons(x):
  q=qs(x);d=q@A.T;phi,three=field(q);return np.concatenate([d-float(LOW),float(HIGH)-d])
 for j,seed in enumerate(starts):
  if time.monotonic()>=start+37:break
  begin=time.monotonic();local_end=min(begin+3,start+37);last=None
  def obj(x):
   nonlocal last
   if time.monotonic()>=local_end:raise TimeBudget()
   a,b=x;q=qs(x);phi,rr,g=field(q,True);dq=np.array([[np.cos(a)*np.cos(b),np.cos(a)*np.sin(b),-np.sin(a)],[-np.sin(a)*np.sin(b),np.sin(a)*np.cos(b),0]])
   last=q;return float(phi*10000),np.asarray(dq@g,dtype=float)*10000
  try:
   opt=minimize(obj,angles(seed),jac=True,method='SLSQP',bounds=[(0,np.pi),(0,2*np.pi)],constraints=[{'type':'ineq','fun':cons}],options={'maxiter':100,'ftol':1e-12});r=record(qs(opt.x),'SLSQP');status={'success':bool(opt.success),'message':str(opt.message),'iterations':int(opt.nit),'result':r}
  except TimeBudget:status={'success':False,'message':'per-start time limit','result':record(last,'SLSQP_last')if last is not None else None}
  local.append({'start_index':j,'seed_q':seed.tolist(),'seconds':time.monotonic()-begin,**status})
 de_start=time.monotonic();de_end=min(de_start+10,deadline-4);debest=[];nevals=0
 def defun(x):
  nonlocal nevals
  if time.monotonic()>=de_end:raise TimeBudget()
  xx=np.asarray(x);xx=xx.reshape(2,-1).T;q=qs(xx);phi,_=field(q);nevals+=len(q)
  if len(q):debest.append((float(phi.min()),q[int(phi.argmin())].copy()))
  return float(phi[0])if np.asarray(x).ndim==1 else np.asarray(phi,dtype=float)
 def decons(x):
  if time.monotonic()>=de_end:raise TimeBudget()
  xx=np.asarray(x);single=xx.ndim==1;xx=xx.reshape(2,-1).T;q=qs(xx);d=q@A.T;phi,rr=field(q);result=np.concatenate([d-float(LOW),float(HIGH)-d],axis=1).T;return result[:,0]if single else result
 de_status='insufficient_feasible_mesh'
 if len(eligible_grid)>=40 and time.monotonic()<de_end:
  init=np.array([angles(q)for q in eligible_grid[np.linspace(0,len(eligible_grid)-1,40,dtype=int)]])
  if best is not None:init[0]=angles(np.array(best['q']))
  try:
   opt=differential_evolution(defun,[(0,np.pi),(0,2*np.pi)],constraints=[NonlinearConstraint(decons,np.zeros(6),np.full(6,np.inf))],init=init,maxiter=100000,tol=1e-10,polish=False,vectorized=True,updating='deferred',seed=2026101733,callback=lambda x,convergence:time.monotonic()>=de_end);record(qs(opt.x),'DE');de_status=str(opt.message)
  except TimeBudget:de_status='10second_or_shared_budget_guard'
 if debest:record(min(debest,key=lambda r:r[0])[1],'DE_best_evaluated')
 de={'seconds':time.monotonic()-de_start,'seconds_limit':10,'objective_evaluations':nevals,'status':de_status}
 # Optional rigorous local point verification, not a lower-bound proof.
 verification=None
 if best is not None and time.monotonic()<deadline-2:
  q0=list(map(lambda x:F(str(x)),best['q']));sign=1 if q0[2]>=0 else-1;x=q0[0]/(1+abs(q0[2]));y=q0[1]/(1+abs(q0[2]));D=1+x*x+y*y;qr=[2*x/D,2*y/D,sign*(1-x*x-y*y)/D];assert sum(x*x for x in qr)==1
  si=I(1-u*u).sqrt();AI=[[I(1),I(0),I(0)],[I(u),si,I(0)],[I(v),I(t-u*v)/si,I(gram).sqrt()/si]];di=[sum(a*I(q)for a,q in zip(anchor,qr))for anchor in AI];iterms=[(e,I(c))for e,c in terms]
  def R(a,b,c):
   powers=[]
   for val in [a,b,c]:
    pw=[I(1)]
    for j in range(27):pw.append(pw[-1]*val)
    powers.append(pw)
   return sum(coeff*powers[0][i]*powers[1][j]*powers[2][k]for(i,j,k),coeff in iterms)
  R3=[R(I(edge),di[a],di[b])for edge,(a,b)in zip(edgevalues,edgepairs)];phi=sum(R3);thresholdI=I(threshold);Kint=I(K);dotallowed=all(z.lo>I(LOW).hi and z.hi<I(HIGH).lo for z in di);individual=all(z.lo>=0 and z.hi<Kint.lo for z in R3);strictbelow=phi.hi<thresholdI.lo
  verification={'interpretation':'Fixed rational T with exact algebraic Cholesky anchors, exact rational sphere q from finite-decimal stereographic projection; I384 outward values. This certifies this specified point only, not the field minimum or six-point packing.','bits':BITS,'q_rational':list(map(str,qr)),'q_norm_squared_exact':str(sum(x*x for x in qr)),'anchor_dot_intervals':[z.bounds()for z in di],'individual_R_intervals':[z.bounds()for z in R3],'phi_interval':phi.bounds(),'threshold_interval':thresholdI.bounds(),'threshold_minus_phi':(thresholdI-phi).bounds(),'all_dot_bounds_strict':dotallowed,'all_individual_old_R_bounds_strict':individual,'phi_total_below_budget_strict':phi.hi<Kint.lo,'phi_below_K_over6_strict':strictbelow,'display_only':{'phi_low':float(F(phi.lo,S)),'phi_high':float(F(phi.hi,S)),'threshold_low':float(F(thresholdI.lo,S)),'threshold_minus_phi_low':float(F((thresholdI-phi).lo,S))}}
 result={'warning':'Numerical field minima are feasible values, hence upper bounds on the true minimum; never certified field lower bounds. One-point strict sub-threshold witness, if present, defeats only the uniform single-field threshold route and is not a Thomson counterexample or six-point extension.','T_decimal':coords,'Gram_exact':str(gram),'Gram_display':float(gram),'anchor_float':A.tolist(),'anchor_float_unit_errors':(np.sum(A*A,axis=1)-1).tolist(),'anchor_float_Gram_matrix':(A@A.T).tolist(),'Cholesky_formula':'a0=(1,0,0);a1=(u,sqrt(1-u*u),0);a2=(v,(t-u*v)/sqrt(1-u*u),sqrt(Gram)/sqrt(1-u*u))','R_old_T_exact':str(rtriangle),'total_old_budget_exact':str(totalbudget),'remaining_six_phi_budget_exact':str(K),'remaining_budget_display':float(K),'one_phi_average_threshold_exact':str(threshold),'one_phi_average_threshold_display':float(threshold),'constraints':'Broad search superset: each anchor dot in[-9957/10000,14/25]; old R>=0 from saved certificate. Remaining-budget constraints are checked and reported, not imposed in optimization, because the initial mesh had no points passing phi<=K. New dot lower bound only necessary for global minimizers','mesh':mesh,'SLSQP':local,'DE':de,'records':rows,'best_numeric_eligible':best,'fixed_point_I384':verification,'numerical_seconds_budget':60,'first_mesh_only_seconds':prior_seconds,'elapsed_seconds':time.monotonic()-start,'cumulative_numerical_seconds':prior_seconds+time.monotonic()-start,'domain_minimum_claimed':False,'dependencies':{str(p):sha(p)for p in [mp,rp,up,BASE/'d12_minimizer_domain2026_results.json',BASE/'dyadic_interval.py',Path(__file__)]}}
 assert result['cumulative_numerical_seconds']<60
 outpath.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k]for k in ['elapsed_seconds','Gram_display','remaining_budget_display','one_phi_average_threshold_display','mesh','DE','best_numeric_eligible']},indent=2),flush=True)
 if verification:print('I384',json.dumps(verification['display_only']),verification['phi_below_K_over6_strict'],flush=True)
 return result
if __name__=='__main__':run()
