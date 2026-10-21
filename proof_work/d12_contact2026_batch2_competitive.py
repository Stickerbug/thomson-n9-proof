"""Additional <=15sec competitive numerical discovery; originalA point checks."""
import time,signal,json
from fractions import Fraction
import numpy as np
from scipy.optimize import minimize
from sharp_boundary_actualf_v3 import random_cond,dedup
from d12_competitive_probe2026_probe import OldResidual

def load_old(root):
 model=json.loads((root/'nonsharp_d10_root25_7599205_v10.json').read_text());upper=json.loads((root/'pair056_optimized_certificate.json').read_text());budget=7*(Fraction(upper['U'])-Fraction(model['target']));return OldResidual(model,budget),float(budget)

def gram(p):
 p=np.atleast_2d(p);return 1+2*np.prod(p,axis=1)-np.sum(p*p,axis=1)

def validate_competitive(comp,x,actual,rng,old,budget,seeds):
 start=time.monotonic();res=comp.kernel(x);pool=[];drawn=0;local=[];timedout=False
 def alarm(*a):raise TimeoutError()
 signal.signal(signal.SIGALRM,alarm);signal.setitimer(signal.ITIMER_REAL,14)
 def keep(p):
  p=dedup(p);return p[(gram(p)>=0)&(old(p)<=budget)] if len(p) else p
 try:
  for _ in range(5):
   p=random_cond(1500,rng);drawn+=len(p);pool.append(keep(p))
   if sum(map(len,pool))>=2500 or time.monotonic()-start>5:break
  pool.append(keep(seeds));scan=dedup(np.vstack(pool));vv=res(scan)
  def fg(p):
   v,g=res(p,True);return float(v[0]),g[0]
  def con(p):return np.array([gram(p)[0],(budget-old(p)[0])/budget,p[1]-p[0],p[2]-p[1]])
  for p in scan[np.argsort(vv)[:6]]:
   if time.monotonic()-start>12:break
   op=minimize(fg,p,jac=True,method='SLSQP',bounds=[(-1,.56)]*3,constraints=[{'type':'ineq','fun':con}],options={'maxiter':60,'ftol':1e-12});q=np.sort(op.x)
   if gram(q)[0]>=0 and old(q)[0]<=budget and q.min()>=-1 and q.max()<=.56:local.append(q)
 except TimeoutError:timedout=True
 finally:signal.setitimer(signal.ITIMER_REAL,0)
 scan=dedup(np.vstack(pool+local)) if local else dedup(np.vstack(pool));vv=res(scan);ix=np.argsort(vv)[:20];points=scan[ix];av=actual(points);ov=old(points)
 rows=[{'point':p.tolist(),'R_compiled':float(v),'R_originalA':float(a),'Gram':float(gram(p)[0]),'old_R':float(o),'old_budget_slack':float(budget-o)}for p,v,a,o in zip(points,vv[ix],av,ov)]
 return {'domain':'Gram>=0,box[-1,.56],old certified residual<=7(U-LB),numeric membership only','budget':budget,'random_drawn':drawn,'eligible_scan_count':len(scan),'seconds':time.monotonic()-start,'timedout':timedout,'worst_points':rows,'minimum_originalA':float(min(av)) if len(av) else None},points
