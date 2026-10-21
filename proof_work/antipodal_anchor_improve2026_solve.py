import os,time,json,numpy as np,scipy.optimize as so,cvxpy as cp
from fractions import Fraction as Fr
from pathlib import Path
from certify_three_point_d4 import add,mul,scale,const,mono,power,ldl
start=time.time();base=Path(__file__).parent;rng=np.random.default_rng(633574)
h=[Fr(v) for v in json.loads((base/'antipodal_anchor_exact_export.json').read_text())['h']];hf=np.array(list(map(float,h)))
H=lambda x:np.polynomial.polynomial.polyval(x,hf)
def rhs(T):
 z,w,t=T.T;return H(t)+(H(z)+H(-z)+H(w)+H(-w))/6
def features(T,d=4):
 z,w,t=T.T;aa=t-z*w;bb=(1-z*z)*(1-w*w);Q=[np.ones(len(z)),aa]
 for k in range(1,d):Q.append(2*aa*Q[-1]-bb*Q[-2])
 out=[];spec=[]
 for k in range(d+1):
  for par in [0,1]:
   ii=np.arange(par,d-k+1,2)
   if not len(ii):continue
   Z=z[:,None]**ii;W=w[:,None]**ii
   F=(Z[:,:,None]*W[:,None,:]+W[:,:,None]*Z[:,None,:])*.5*Q[k][:,None,None]
   di=ii[:,None]+ii[None,:];dz=z[:,None,None]**di*(1-z*z)[:,None,None]**k;dw=w[:,None,None]**di*(1-w*w)[:,None,None]**k
   out.append(F+(dz+dw)/12);spec.append((k,ii.tolist()))
 return out,spec
def fromq(z,w,a):return np.c_[z,w,z*w+np.sqrt((1-z*z)*(1-w*w))*np.cos(a)]
z=rng.uniform(-.63,.63,6500);w=rng.uniform(-.63,.63,6500);a=rng.uniform(0,np.pi,6500);T=fromq(z,w,a)
zz,ww=np.meshgrid(np.linspace(-.63,.63,65),np.linspace(-.63,.63,65));Z=zz.ravel();W=ww.ravel()
T=np.r_[T,fromq(Z,W,np.zeros(len(Z))),fromq(Z,W,np.full(len(Z),np.pi))]
for sign in [-1,1]:
 z=rng.uniform(-.63,.63,1200);w=sign*z+rng.normal(0,.01,1200);w=np.clip(w,-.63,.63);a=rng.uniform(0,np.pi,1200);T=np.r_[T,fromq(z,w,a)]
T=T[T[:,2]<=.57];Fs,spec=features(T);A=[cp.Variable((v.shape[1],v.shape[1]),symmetric=True) for v in Fs];c=cp.Variable()
e=sum(v.reshape(len(T),-1)@cp.vec(a,order='C')for v,a in zip(Fs,A))
prob=cp.Problem(cp.Maximize(c),[a>>0 for a in A]+[e+c<=rhs(T),sum(cp.trace(a)for a in A)<=1000])
t0=time.time();prob.solve(solver='CLARABEL',time_limit=85,max_iter=130,tol_gap_abs=2e-9,tol_feas=2e-9,tol_gap_rel=2e-9)
ans={'degree':4,'training_count':len(T),'status':prob.status,'solver_seconds':time.time()-t0,'domain':'abs(z),abs(w)<=.63;t<=.57;Gram>=0','h':list(map(str,h))}
if c.value is None:ans['failure']='no solver values';(base/'antipodal_anchor_improve2026_result.json').write_text(json.dumps(ans,indent=2));print(ans);raise SystemExit
V=[v.value for v in A];ans.update(c=float(c.value),sampled_bound=.5+21*float(c.value),trace=sum(float(np.trace(a))for a in V),min_eig=min(float(np.linalg.eigvalsh(a)[0])for a in V),matrices=[v.tolist()for v in V])
def residual(T):return rhs(T)-sum(np.einsum('nij,ij->n',v,a)for v,a in zip(features(T)[0],V))-float(c.value)
scan=time.time();z=rng.uniform(-.63,.63,50000);w=rng.uniform(-.63,.63,50000);a=rng.uniform(0,np.pi,50000);S=fromq(z,w,a);S=S[S[:,2]<=.57];rr=residual(S);ans['random_min']=float(rr.min());ans['random_witness']=S[np.argmin(rr)].tolist()
def fun(q):
 z,w,a=q;T=fromq(np.array([z]),np.array([w]),np.array([a]));return float(residual(T)[0]) if T[0,2]<=.57 else 10+(T[0,2]-.57)*100
s=so.differential_evolution(fun,[(-.63,.63),(-.63,.63),(0,np.pi)],seed=3757,popsize=10,maxiter=90,tol=1e-8,polish=True,callback=lambda *args:time.time()-scan>8)
ans['de_min']=float(s.fun);ans['de_q']=s.x.tolist();ans['scan_seconds']=time.time()-scan;ans['not_rigorous_adjusted_diagnostic']=ans['sampled_bound']+21*min(0,ans['de_min'],ans['random_min'])
(base/'antipodal_anchor_improve2026_result.json').write_text(json.dumps(ans,indent=2));print({k:v for k,v in ans.items()if k not in ['matrices','h']},flush=True)
# Quantize and exact-LDL once; independent of numerical solver success claims.
As=[];piv=[]
for raw in V:
 n=len(raw);a=[[Fr(str(round((raw[i,j]+raw[j,i])/2,9)))+Fr(i==j,10**6)for j in range(n)]for i in range(n)];piv.append(ldl(a));As.append(a)
z,w,t=[mono(j,1)for j in range(3)];aa=add(t,scale(mul(z,w),-1));bb=mul(add(const(1),scale(power(z,2),-1)),add(const(1),scale(power(w,2),-1)));Q=[const(1),aa]
for k in range(1,4):Q.append(add(scale(mul(aa,Q[-1]),2),scale(mul(bb,Q[-2]),-1)))
K={};D={};blocks=[]
for (k,ii),a in zip(spec,As):
 blocks.append({'k':k,'powers':ii,'A':[[str(v)for v in row]for row in a]})
 for i,p in enumerate(ii):
  for j,q in enumerate(ii):
   K=add(K,scale(mul(mul(mono(0,p),mono(1,q)),Q[k]),a[i][j]));D=add(D,scale(mul(mono(0,p+q),power(add(const(1),scale(power(z,2),-1)),k)),a[i][j]))
target=Fr('25.82');cc=(target-Fr(1,2))/21;fields={}
for j,v in enumerate(h):
 fields=add(fields,{(0,0,j):v})
 for axis in [0,1]:fields=add(fields,scale(mono(axis,j),v*Fr(1+(-1)**j,6)))
Dw={(0,a[0],0):v for a,v in D.items()};R=add(fields,scale(K,-1),scale(add(D,Dw),-Fr(1,12)),const(-cc))
ex={'degree':4,'target':str(target),'c':str(cc),'blocks':blocks,'h':list(map(str,h)),'psd_ldl_pivots':piv,'kernel_monomial':[[list(a),str(v)]for a,v in K.items()],'diag_z_monomial':[[list(a),str(v)]for a,v in D.items()],'residual_monomial':[[list(a),str(v)]for a,v in R.items()],'domain':'abs(z),abs(w)<=.63;t in [-1,.57];Gram>=0','note':'unverified proposal only; target may need lowering'}
(base/'antipodal_anchor_improve2026_export.json').write_text(json.dumps(ex,indent=2));print('exact LDL export complete',time.time()-start,flush=True)
