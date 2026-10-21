"""Finite sample pair PSD discovery only; no rigorous lower bound."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import json,time
from pathlib import Path
import numpy as np
import cvxpy as cp
from external_pair_field2026_probe import Residual
P=Path(__file__).parent
row=json.loads((P/'external_pair_field2026_summary.json').read_text())['rows'][0]
R=Residual(json.loads((P/'nonsharp_d10_root25_7599205_v10.json').read_text()))
anchors=np.array(row['anchors_float']);edges=np.array(list(map(float,row['triangle_decimal'])))
rng=np.random.default_rng(5719)
def sample(n):
 out=[];count=0
 while count<n:
  z=rng.normal(size=(max(2*(n-count),200),2,3));z/=np.linalg.norm(z,axis=2)[:,:,None]
  mask=(np.max(z@anchors.T,axis=(1,2))<=.56)&(np.sum(z[:,0]*z[:,1],axis=1)<=.56)
  z=z[mask][:n-count];out.append(z);count+=len(z)
 return np.concatenate(out)
def features(q):
 x,y,z=q.T
 return np.stack([x,y,z,x*y,x*z,y*z,x*x-y*y,3*z*z-1],axis=1)
def value(z):
 q,r=z[:,0],z[:,1];dq=q@anchors.T;dr=r@anchors.T;s=np.sum(q*r,axis=1);pairs=[(0,1),(0,2),(1,2)]
 triples=np.stack([np.stack([np.full(len(q),edges[k]),d[:,a],d[:,b]],axis=1)for d in [dq,dr]for k,(a,b)in enumerate(pairs)]+[np.stack([dq[:,a],dr[:,a],s],axis=1)for a in range(3)],axis=1)
 v=R(triples.reshape(-1,3)).reshape(-1,9)
 return (v[:,:6].sum(axis=1)/5+v[:,6:].sum(axis=1))*1e5
start=time.monotonic();train=np.concatenate([sample(2200),np.array([[row['best']['q'],row['best']['r']]])]);values=value(train)
q,r=features(train[:,0]),features(train[:,1])
C=(np.einsum('ni,nj->nij',q,r)+np.einsum('ni,nj->nij',r,q))/2+(np.einsum('ni,nj->nij',q,q)+np.einsum('ni,nj->nij',r,r))/10
A=cp.Variable((8,8),symmetric=True);beta=cp.Variable()
problem=cp.Problem(cp.Maximize(beta-1e-8*cp.trace(A)),[A>>0,cp.reshape(C,(len(C),64),order='C')@cp.reshape(A,(64,),order='C')+beta<=values,cp.trace(A)<=1000])
problem.solve(solver='CLARABEL',max_iter=70,time_limit=80,tol_gap_abs=1e-7,tol_feas=1e-8,tol_gap_rel=1e-8)
out={'status':'finite_sample_discovery_only','warning':'No continuous-domain lower bound; random validation is not proof.','solver_status':problem.status,'iterations':problem.solver_stats.num_iters,'scale':100000,'features':['x','y','z','xy','xz','yz','x^2-y^2','3z^2-1'],'alpha':0,'training_count':len(train),'threshold':row['best']['threshold_K_over_15'],'identity':'sum15[viAvj+(di+dj)/10]=0.5(sumvi)A(sumvi)'}
if A.value is not None:
 a=A.value;b=float(beta.value);test=sample(5000);tv=value(test);q,r=features(test[:,0]),features(test[:,1]);cor=np.einsum('ni,ij,nj->n',q,a,r)+(np.einsum('ni,ij,nj->n',q,a,q)+np.einsum('ni,ij,nj->n',r,a,r))/10;slack=tv-cor-b
 out.update(A_scaled=a.tolist(),beta_scaled=b,beta=b/1e5,min_eigenvalue=float(min(np.linalg.eigvalsh(a))),trace=float(np.trace(a)),training_min_slack=float(min(values-np.einsum('nij,ij->n',C,a)-b)),independent_count=len(test),independent_min_slack=float(min(slack)),independent_violations=int(sum(slack<-1e-7)),independent_min_W=float(min(tv)/1e5),independent_worst_pair=test[np.argmin(slack)].tolist())
out['total_seconds']=time.monotonic()-start
(P/'sixq_dual2026_t2_bash_proposal.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items()if k!='A_scaled'},indent=2))
