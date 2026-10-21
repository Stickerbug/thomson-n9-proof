"""Finite numerical discovery only: no sampled value is a certified lower bound."""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
import time,json,hashlib
import numpy as np
from scipy.optimize import minimize,differential_evolution
from scipy.spatial import cKDTree
BASE=Path(__file__).parent
TRIPLES=[('T2',['.3464802927157662','.3464805531965182','.34648072472904085']),('T3',['-.07134886362384837','.3392793442065059','.3392793442065059'])]
MODEL=BASE/'nonsharp_d10_root25_7599205_v10.json'
raw=json.loads(MODEL.read_text());terms=[(tuple(e),F(z))for e,z in raw['residual_monomial']]
def angles(q):return np.array([np.arccos(np.clip(q[2],-1,1)),np.arctan2(q[1],q[0])%(2*np.pi)])
def qs(x):
 x=np.asarray(x);a,b=x[...,0],x[...,1]
 return np.stack([np.sin(a)*np.cos(b),np.sin(a)*np.sin(b),np.cos(a)],axis=-1)
def work(name,coords):
 start=time.monotonic();u,v,t=map(float,coords);g=1+2*u*v*t-u*u-v*v-t*t
 anchors=np.array([[1.,0,0],[u,np.sqrt(1-u*u),0],[v,(t-u*v)/np.sqrt(1-u*u),np.sqrt(g)/np.sqrt(1-u*u)]])
 cs=[]
 for edge in [u,v,t]:
  c=np.zeros((28,28),dtype=np.longdouble)
  for (i,j,k),z in terms:c[j,k]+=np.longdouble(z.numerator)/np.longdouble(z.denominator)*np.longdouble(edge)**i
  cs.append(c)
 def field(q):
  d=np.asarray(q,dtype=np.longdouble)@np.asarray(anchors.T,dtype=np.longdouble)
  return sum(np.polynomial.polynomial.polyval2d(d[...,i],d[...,j],c)for (i,j),c in zip([(0,1),(0,2),(1,2)],cs))
 ff=list(map(F,coords));rr=sum(z*ff[0]**i*ff[1]**j*ff[2]**k for (i,j,k),z in terms)
 K=7*(F('25.75998653126983156407570227376049402866')-F(raw['target']))-rr
 n=20000;z=1-2*(np.arange(n)+.5)/n;az=np.arange(n)*np.pi*(3-np.sqrt(5));rad=np.sqrt(1-z*z)
 grid=np.array([rad*np.cos(az),rad*np.sin(az),z]).T;grid=grid[np.max(grid@anchors.T,axis=1)<=.56];vals=field(grid)
 neigh=cKDTree(grid).query(grid,k=14)[1];indices=np.flatnonzero(np.all(vals[:,None]<=vals[neigh],axis=1));indices=sorted(indices,key=lambda i:vals[i])[:12]
 wells=[]
 for ix in indices:
  res=minimize(lambda x:float(field(qs(x))),angles(grid[ix]),method='SLSQP',constraints=[{'type':'ineq','fun':lambda x:.56-qs(x)@anchors.T}],bounds=[(0,np.pi),(0,2*np.pi)],options={'ftol':1e-14,'maxiter':150})
  q=qs(res.x);value=float(field(q))
  if np.max(q@anchors.T)>.5600000001:continue
  if any(np.dot(q,row['q'])>.999 for row in wells):continue
  wells.append({'q':q.tolist(),'phi':value,'optimizer_success':bool(res.success),'anchor_max':float(np.max(q@anchors.T))})
 wells.sort(key=lambda x:x['phi']);centers=np.array([x['q']for x in wells])*.9999999
 dotcaps=grid@centers.T;sample_min=float(vals.min());proposals=[]
 for nc in [1,2,3]:
  best=None
  for ids in combinations(range(len(wells)),nc):
   outside=np.max(dotcaps[:,ids],axis=1)<=.89
   if not np.any(outside):continue
   M=float(vals[outside].min());L=nc*sample_min+(6-nc)*M
   row={'cap_count':nc,'well_indices':list(ids),'global_sample_min':sample_min,'outside_sample_min':M,'hypothetical_six_lower_if_bounds_proved':L,'hypothetical_margin':L-float(K),'cap_centers':centers[list(ids)].tolist(),'outside_grid_witness':grid[outside][np.argmin(vals[outside])].tolist()}
   if best is None or L>best['hypothetical_six_lower_if_bounds_proved']:best=row
  if best:proposals.append(best)
 output={'name':name,'triangle_decimal':coords,'gram':g,'anchor_unit_errors':(np.linalg.norm(anchors,axis=1)-1).tolist(),'R_old_exact':str(rr),'budget_exact':str(K),'budget_display':float(K),'grid_total':n,'allowed_grid':len(grid),'global_sample_min':sample_min,'global_sample_witness':grid[np.argmin(vals)].tolist(),'wells':wells,'cap_proposals':proposals,'DE':[]}
 print('MESH',name,json.dumps({k:v for k,v in output.items()if k not in ['R_old_exact','budget_exact']}),flush=True)
 for mode,seed in [('global',2102),('outside2',2103),('outside3',2104)]:
  proposal=next((p for p in proposals if p['cap_count']==int(mode[-1])),None)if mode!='global'else None
  if mode!='global'and proposal is None:continue
  cap=np.array(proposal['cap_centers'])if proposal else None
  def objective(xx):
   q=qs(np.asarray(xx).T);pen=np.maximum(0,np.max(q@anchors.T,axis=-1)-.56)
   if cap is not None:pen+=np.maximum(0,np.max(q@cap.T,axis=-1)-.89)
   return np.asarray(field(q)+100*pen,dtype=float)
  res=differential_evolution(objective,[(0,np.pi),(0,2*np.pi)],seed=seed,popsize=20,maxiter=150,tol=1e-10,polish=False,vectorized=True,updating='deferred');q=qs(res.x)
  row={'mode':mode,'seed':seed,'q':q.tolist(),'phi':float(field(q)),'anchor_max':float(np.max(q@anchors.T)),'cap_max':float(np.max(q@cap.T))if cap is not None else None,'objective':float(res.fun)}
  output['DE'].append(row);print('DE',name,json.dumps(row),flush=True)
 output['seconds']=time.monotonic()-start
 return output
if __name__=='__main__':
 start=time.monotonic();result={'status':'numerical_discovery_only_not_lower_bounds','warning':'Every reported field minimum is a feasible numerical value, hence an upper bound on the true minimum. Cap counting formulas are hypothetical until rigorous full-domain certification.','model':str(MODEL),'model_sha256':hashlib.sha256(MODEL.read_bytes()).hexdigest(),'results':[]}
 for name,coords in TRIPLES:result['results'].append(work(name,coords))
 result['seconds']=time.monotonic()-start;out=BASE/'two_other_valleys2026_probe.json';out.write_text(json.dumps(result,indent=2)+'\n');print('SAVED',out,'seconds',result['seconds'],flush=True)
