import numpy as np, scipy.optimize as so, cvxpy as cp, json, time
from pathlib import Path
rng=np.random.default_rng(9122026)

def obj(q,grad=False):
 z=q[:7];a=q[7:];rho=np.sqrt(1-z*z);x=np.c_[rho*np.cos(a),rho*np.sin(a),z]
 X=np.r_[x,[[0,0,1],[0,0,-1]]];D=X[:,None,:]-X[None,:,:];r=np.linalg.norm(D,axis=2);np.fill_diagonal(r,np.inf)
 E=np.sum(1/r)/2;G=-np.sum(D/r[:,:,None]**3,axis=1)[:7]
 dz=np.c_[-z/rho*np.cos(a),-z/rho*np.sin(a),np.ones(7)];da=np.c_[-rho*np.sin(a),rho*np.cos(a),np.zeros(7)]
 return E,np.r_[np.sum(G*dz,axis=1),np.sum(G*da,axis=1)]
runs=[];best=None
for j in range(48):
 q=np.r_[rng.uniform(-.55,.55,7),rng.uniform(0,2*np.pi,7)]
 s=so.minimize(obj,q,jac=True,method='L-BFGS-B',bounds=[(-.999,.999)]*7+[(None,None)]*7,options={'ftol':2e-14,'gtol':1e-9,'maxiter':1200})
 runs.append(float(s.fun))
 if best is None or s.fun<best.fun:best=s
print('actual',best.fun, 'levels', sorted(set(round(x,8) for x in runs)),flush=True)
Path('proof_work/antipodal_actual_numerics.json').write_text(json.dumps({'energy':float(best.fun),'q':best.x.tolist(),'gradient':float(np.linalg.norm(best.jac)),'runs':runs,'note':'numerical multistart only; not global proof'},indent=2))

def triples(n):
 z=rng.uniform(-.56,.56,n);w=rng.uniform(-.56,.56,n);a=rng.uniform(0,np.pi,n);t=z*w+np.sqrt((1-z*z)*(1-w*w))*np.cos(a)
 return np.c_[z,w,t][t<=.56]

def features(T,d):
 z,w,t=T.T;q0=np.ones(len(z));q1=t-z*w;Qs=[q0,q1]
 for k in range(1,d):Qs.append(2*q1*Qs[-1]-(1-z*z)*(1-w*w)*Qs[-2])
 out=[]
 for k in range(d+1):
  n=d-k+1
  for parity in [0,1]:
   ii=np.arange(parity,n,2)
   if len(ii)==0:continue
   Z=z[:,None]**ii;W=w[:,None]**ii
   F=(Z[:,:,None]*W[:,None,:]+W[:,:,None]*Z[:,None,:])*.5*Qs[k][:,None,None]
   Dz=z[:,None,None]**(ii[:,None]+ii[None,:])*(1-z*z)[:,None,None]**k
   Dw=w[:,None,None]**(ii[:,None]+ii[None,:])*(1-w*w)[:,None,None]**k
   out.append(F+(Dz+Dw)/12)
 return out

def rhs(T):
 z,w,t=T.T
 v=lambda z:1/np.sqrt(2-2*z)+1/np.sqrt(2+2*z)
 return 1/np.sqrt(2-2*t)+(v(z)+v(w))/6

res=[]
for d in [3,5]:
 train=triples(2200);train=np.r_[train,[[-.56,-.56,-.3728],[0,0,-1],[0,0,.56],[.56,-.56,-1],[.56,.56,.56]]]
 # Drop infeasible explicit extra points if any.
 train=train[1+2*np.prod(train,axis=1)-np.sum(train*train,axis=1)>=-1e-12]
 for it in range(4):
  Fs=features(train,d);A=[cp.Variable((v.shape[1],v.shape[1]),symmetric=True) for v in Fs];c=cp.Variable();con=[a>>0 for a in A]
  expr=sum(cp.reshape(v,(len(train),-1),order='C')@cp.vec(a,order='C') for v,a in zip(Fs,A))
  con += [expr+c<=rhs(train),sum(cp.trace(a) for a in A)<=5000]
  pr=cp.Problem(cp.Maximize(c),con)
  try:pr.solve(solver='CLARABEL',max_iter=150,tol_gap_abs=1e-9,tol_feas=1e-9,tol_gap_rel=1e-9)
  except Exception as e:print('solver failed',d,it,str(e),flush=True);break
  if any(a.value is None for a in A):print('no values',pr.status,flush=True);break
  vals=[a.value for a in A]
  def residual(T):return rhs(T)-sum(np.einsum('nij,ij->n',v,a) for v,a in zip(features(T,d),vals))-float(c.value)
  def dec(q):
   z,w,alpha=q;t=z*w+np.sqrt((1-z*z)*(1-w*w))*np.cos(alpha)
   return np.array([[z,w,t]])
  def bad(q):
   T=dec(q)
   if T[0,2]>.56:return 1000+(T[0,2]-.56)*100
   return residual(T)[0]
  cuts=[];mins=[]
  for seed in [81,94]:
   de=so.differential_evolution(bad,[(-.56,.56),(-.56,.56),(0,np.pi)],seed=seed,popsize=14,maxiter=220,tol=1e-9,polish=True)
   cuts.append(dec(de.x)[0]);mins.append(float(de.fun))
  test=triples(22000);rr=residual(test);inds=np.argsort(rr)[:100];cuts.extend(test[inds])
  record={'degree':d,'iteration':it,'c':float(c.value),'energy_bound_sampled':.5+21*float(c.value),'de_min':min(mins),'random_min':float(rr.min()),'status':pr.status,'trace':sum(float(np.trace(a)) for a in vals),'min_eig':min(float(np.linalg.eigvalsh(a)[0]) for a in vals),'matrices':[a.tolist() for a in vals],'cuts':np.array(cuts[:2]).tolist()}
  res.append(record);print({k:v for k,v in record.items() if k not in ['matrices','cuts']},flush=True)
  Path('proof_work/antipodal_anchor_results.json').write_text(json.dumps(res,indent=2))
  train=np.r_[train,np.array(cuts)]
