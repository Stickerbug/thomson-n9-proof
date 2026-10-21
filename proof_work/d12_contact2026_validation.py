import time,signal
import numpy as np
from scipy.optimize import differential_evolution,NonlinearConstraint,minimize
from sharp_boundary_actualf_v3 import random_cond,boundary_points,dedup,valid

def validate(comp,xx,rng,iteration,degree):
 start=time.monotonic();res=comp.kernel(xx);random=random_cond(1500,rng);bd=boundary_points(500,rng);points=dedup(np.vstack([random,bd]));values=res(points);found=[points[np.argsort(values)[:60]]];rows=[]
 def record(p,kind):
  p=np.asarray(p);v=float(res(p)[0]);d={'kind':kind,'residual':v,'triangle':p.tolist(),'gram_determinant':float(1+2*np.prod(p)-p@p)}
  if valid(p)[0]:rows.append(d);found.append(p[None])
 def con(p):
  u,v,t=np.asarray(p);return np.array([1+2*u*v*t-u*u-v*v-t*t,v-u,t-v])
 def vc(p):
  p=np.asarray(p);single=p.ndim==1;p=p[:,None]if single else p;u,v,t=p;z=np.vstack([1+2*u*v*t-u*u-v*v-t*t,v-u,t-v]);return z[:,0]if single else z
 def obj(p):
  p=np.asarray(p);return float(res(p)[0])if p.ndim==1 else res(p.T)
 def alarm(*args):raise TimeoutError()
 signal.signal(signal.SIGALRM,alarm);signal.setitimer(signal.ITIMER_REAL,max(.1,16-(time.monotonic()-start)))
 try:
  de=differential_evolution(obj,[(-1,.56)]*3,constraints=(NonlinearConstraint(vc,0,np.inf),),vectorized=True,updating='deferred',popsize=12,maxiter=90,polish=False,seed=121000+iteration,x0=points[np.argmin(values)]);record(de.x,'DE')
  def fg(p):
   v,g=res(p,True);return float(v[0]),g[0]
  for p in points[np.argsort(values)[:10]]:
   if time.monotonic()-start>14:break
   op=minimize(fg,p,jac=True,method='SLSQP',bounds=[(-1,.56)]*3,constraints=[{'type':'ineq','fun':con}],options={'maxiter':70,'ftol':1e-13});record(op.x,'local')
 except TimeoutError:pass
 finally:signal.setitimer(signal.ITIMER_REAL,0)
 for p in points[np.argsort(values)[:12]]:record(p,'random')
 rows.sort(key=lambda x:x['residual']);return {'seconds':time.monotonic()-start,'random_count':1500,'boundary_count':500,'independent_minimum':rows[0]['residual'],'worst_points':rows[:20]},dedup(np.vstack(found))
