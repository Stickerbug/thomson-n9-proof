"""GLOBAL MINIMIZER necessary domain, numerical discovery only."""
import time,signal
import numpy as np
from scipy.optimize import minimize,differential_evolution,NonlinearConstraint
from sharp_boundary_actualf_v3 import random_cond,dedup as base_dedup
LOW=-.9957
OLD=None
BUDGET=None

def set_domain(old,budget):
 global OLD,BUDGET
 OLD=old;BUDGET=budget

def gram(p):
 p=np.atleast_2d(p);return 1+2*np.prod(p,axis=1)-np.sum(p*p,axis=1)

def clean(p):
 assert OLD is not None
 p=base_dedup(p)
 if not len(p):return p
 return p[(p.min(axis=1)>=LOW)&(p.max(axis=1)<=.56)&(gram(p)>=0)&(OLD(p)<=BUDGET)]

def validate(comp,x,rng,iteration,degree):
 start=time.monotonic();res=comp.kernel(x);pool=[];rows=[];local=[];drawn=0
 def alarm(*a):raise TimeoutError()
 signal.signal(signal.SIGALRM,alarm);signal.setitimer(signal.ITIMER_REAL,11)
 try:
  for _ in range(10):
   q=random_cond(1800,rng);drawn+=len(q);pool.append(clean(q))
   if sum(map(len,pool))>=3000 or time.monotonic()-start>3:break
  scan=clean(np.vstack(pool));vv=res(scan)
  def con(p):
   p=np.asarray(p);single=p.ndim==1;p=p.reshape(3,-1).T
   ans=np.vstack([gram(p),(BUDGET-OLD(p))/BUDGET,p[:,1]-p[:,0],p[:,2]-p[:,1]])
   return ans[:,0] if single else ans
  def objective(p):return float(res(p)[0]) if np.ndim(p)==1 else res(p.T)
  de=differential_evolution(objective,[(LOW,.56)]*3,constraints=[NonlinearConstraint(con,0,np.inf)],popsize=10,maxiter=35,polish=False,vectorized=True,updating='deferred',seed=20261023+iteration,x0=scan[np.argmin(vv)])
  local.append(de.x)
  def fg(p):
   v,g=res(p,True);return float(v[0]),g[0]
  for p in scan[np.argsort(vv)[:8]]:
   if time.monotonic()-start>9:break
   op=minimize(fg,p,jac=True,method='SLSQP',bounds=[(LOW,.56)]*3,constraints=[{'type':'ineq','fun':con}],options={'maxiter':70,'ftol':1e-13});local.append(op.x)
 except TimeoutError:pass
 finally:signal.setitimer(signal.ITIMER_REAL,0)
 scan=clean(np.vstack(pool+[np.atleast_2d(p) for p in local]));v=res(scan);take=np.argsort(v)[:40];points=scan[take]
 for p,a in zip(points,v[take]):rows.append({'triangle':p.tolist(),'residual':float(a),'gram_determinant':float(gram(p)[0]),'old_budget_slack':float(BUDGET-OLD(p)[0])})
 return {'seconds':time.monotonic()-start,'domain':'GLOBAL MINIMIZER ONLY: dots>=-.9957,Gram>=0,oldR<=7gap','random_drawn':drawn,'eligible_count':len(scan),'independent_minimum':float(min(v)),'worst_points':rows},points
