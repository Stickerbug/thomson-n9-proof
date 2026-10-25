import itertools, numpy as np, cvxpy as cp
from scipy.optimize import differential_evolution
N=10; H=.422687424043986066; E=32.71694946014759

def kernels(points,d):
 out=[np.zeros((len(points),d-k+1,d-k+1)) for k in range(d+1)]
 for perm in itertools.permutations(range(3)):
  u,v,t=points[:,perm].T; a=t-u*v; b=(1-u*u)*(1-v*v); q=[np.ones(len(points))]
  if d:q.append(a)
  for k in range(1,d):q.append(2*a*q[-1]-b*q[-2])
  for k in range(d+1):
   p=np.arange(d-k+1); z=u[:,None]**p; w=v[:,None]**p
   out[k]+=q[k][:,None,None]*z[:,:,None]*w[:,None,:]/6
 return out

def design(points,d):
 s=kernels(points,d); rep=[kernels(np.c_[np.ones(len(points)),points[:,j],points[:,j]],d) for j in range(3)]
 return [8*s[k]+sum(x[k] for x in rep) for k in range(d+1)]

def candidate(d):
 r=np.sqrt(1-H*H); X=[[0,0,1],[0,0,-1]]+[[r*np.cos(2*np.pi*j/4),r*np.sin(2*np.pi*j/4),-H] for j in range(4)]+[[r*np.cos(2*np.pi*j/4+np.pi/4),r*np.sin(2*np.pi*j/4+np.pi/4),H] for j in range(4)];X=np.array(X);G=X@X.T
 cand=np.unique(np.round([[G[i,j],G[i,k],G[j,k]] for i,j,k in itertools.combinations(range(N),3)],12),axis=0)
 allp=np.array([[G[i,j],G[i,k],G[j,k]] for i,j,k in itertools.product(range(N),repeat=3)])
 raw=kernels(allp,d); null=[]; ev=[]
 for k in range(d+1):
  M=raw[k].sum(axis=0); ee,U=np.linalg.eigh((M+M.T)/2);ev.append(ee); null.append(U[:,ee<1e-8])
 return cand,null,ev

def sample(n,rng):
 u=rng.uniform(-1,1,n);v=rng.uniform(-1,1,n);th=rng.uniform(0,np.pi,n);t=u*v+np.sqrt((1-u*u)*(1-v*v))*np.cos(th);return np.c_[u,v,t]
def structured():
 out=[]
 for u in np.linspace(-1,1,11):
  for v in np.linspace(-1,1,11):
   rad=np.sqrt(max(0,(1-u*u)*(1-v*v)))
   for th in np.linspace(0,np.pi,3):out.append([u,v,u*v+rad*np.cos(th)])
 return np.array(out)
def hermite():
 r=H;nodes=np.array([-1,-r,r,r*r,2*r*r-1,-r*r+(1-r*r)/np.sqrt(2),-r*r-(1-r*r)/np.sqrt(2)]);x=np.repeat(np.sort(nodes),2);m=len(x);Q=np.zeros((m,m)); f=lambda t:(2-2*t)**-.5; fp=lambda t:(2-2*t)**-1.5
 for i in range(m):
  Q[i,0]=f(x[i]);
  if i: Q[i,1]=fp(x[i]) if x[i]==x[i-1] else (Q[i,0]-Q[i-1,0])/(x[i]-x[i-1])
  for j in range(2,i+1):Q[i,j]=(Q[i,j-1]-Q[i-1,j-1])/(x[i]-x[i-j])
 c=np.diag(Q)
 def Hf(t):
  t=np.asarray(t);z=np.zeros_like(t)+c[-1]
  for j in range(m-2,-1,-1):z=c[j]+(t-x[j])*z
  return z
 return Hf

def run(d, rounds=2):
 rng=np.random.default_rng(9100+d); Hf=hermite(); cand,null,ev=candidate(d); print('degree',d,'cand',len(cand),'shapes',[x.shape for x in null])
 pts=np.vstack([sample(100,rng),structured(),cand]); rawc=design(cand,d)
 B={k:cp.Variable((null[k].shape[1],null[k].shape[1]),symmetric=True) for k in range(d+1) if null[k].shape[1]}
 c=cp.Variable(); f111=cp.sum(np.ones((1,d+1))@null[0]@B[0]@null[0].T@np.ones((d+1,1))); obj=15*c-(5/3)*f111
 def mats(P):
  raw=design(P,d);return {k:np.einsum('ai,nab,bj->nij',null[k],raw[k],null[k]) for k in B}
 for it in range(rounds):
  M=mats(pts);Mc=mats(cand);rhs=np.sum(Hf(pts),axis=1);rhsc=np.sum(Hf(cand),axis=1)
  lhs=c+sum(cp.sum(cp.multiply(M[k].reshape(len(pts),-1),cp.reshape(B[k],(1,B[k].size),order='C')),axis=1) for k in B)
  lc=c+sum(cp.sum(cp.multiply(Mc[k].reshape(len(cand),-1),cp.reshape(B[k],(1,B[k].size),order='C')),axis=1) for k in B)
  con=[b>>0 for b in B.values()]+[lhs<=rhs,lc==rhsc]
  prob=cp.Problem(cp.Maximize(obj),con);prob.solve(solver='CLARABEL',tol_gap_abs=2e-9,tol_gap_rel=2e-9,tol_feas=2e-9,max_iter=250)
  vals={k:B[k].value for k in B};
  def evp(P):
   MM=mats(P);return np.sum(Hf(P),axis=1)-float(c.value)-sum(np.einsum('nij,ij->n',MM[k],vals[k]) for k in B)
  test=sample(5000,rng);res=evp(test)
  def fun(z):
   u,v,th=z;t=u*v+np.sqrt(max(0,(1-u*u)*(1-v*v)))*np.cos(th);return float(evp(np.array([[u,v,t]]))[0])
  de=differential_evolution(fun,[(-1,1),(-1,1),(0,np.pi)],seed=2100+d+it,popsize=8,maxiter=45,polish=True)
  print('it',it,'status',prob.status,'obj',float(prob.value),'gap',E-float(prob.value),'min',float(res.min()),'de',float(de.fun),'eig',min(np.linalg.eigvalsh(x).min() for x in vals.values()),'depoint',de.x,flush=True)
  u,v,th=de.x;t=u*v+np.sqrt(max(0,(1-u*u)*(1-v*v)))*np.cos(th);pts=np.vstack([pts,test[np.argsort(res)[:200]],[u,v,t]])
for d in (8,10): run(d,2)
