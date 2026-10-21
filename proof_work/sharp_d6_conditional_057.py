"""NONRIGOROUS analytic d6 contact+PSD, no finite differences. Trace cap=1e4."""
import json,itertools,time
from pathlib import Path
from fractions import Fraction as F
import numpy as np
import cvxpy as cp
from scipy.optimize import differential_evolution
from candidate_low_rank import features,nullspace_two_rows
from certify_three_point_d4 import const,add,scale,mul,mono,permute,diag
from sharp_three_point import candidate_data,ENERGY,from_angles
from three_point_sampled import minorant,design,sample_triangles
OUT=Path(__file__).with_suffix('.json')
LIMIT=.57
def conditional_samples(count,rng):
 batches=[];total=0
 while total<count:
  a=sample_triangles(max(count,1000),rng);a=a[np.max(a,axis=1)<=LIMIT];batches.append(a);total+=len(a)
 return np.vstack(batches)[:count]
def polynomials(N):
 u,v,t=(mono(i,1)for i in range(3));a=add(t,scale(mul(u,v),-1));b=mul(add(const(1),scale(mul(u,u),-1)),add(const(1),scale(mul(v,v),-1)))
 Q=[const(1),a]
 for k in range(1,6):Q.append(add(scale(mul(a,Q[-1]),2),scale(mul(b,Q[-2]),-1)))
 raw=[]
 for k in range(7):
  block=[]
  for i in range(7-k):
   row=[]
   for j in range(7-k):
    p=mul(mul(mono(0,i),mono(1,j)),Q[k]);s=scale(add(*(permute(p,pm)for pm in itertools.permutations(range(3)))),F(1,6))
    row.append(add(scale(s,7),*(diag(s,axis)for axis in range(3)),const(F(1,8)if k==0 else 0)))
   block.append(row)
  raw.append(block)
 result=[];indices=[]
 for k,n in enumerate(N):
  for i in range(n.shape[1]):
   for j in range(i,n.shape[1]):
    p={}
    for aa in range(n.shape[0]):
     for bb in range(n.shape[0]):p=add(p,scale(raw[k][aa][bb],n[aa,i]*n[bb,j]+(n[aa,j]*n[bb,i]if i!=j else 0)))
    result.append(p);indices.append((k,i,j))
 return result,indices
def evaluate(P,points,axis=None):
 out=np.zeros((len(points),len(P)))
 for j,p in enumerate(P):
  for powers,c in p.items():
   powers=list(powers);c=float(c)
   if axis is not None:
    c*=powers[axis];powers[axis]-=1
    if c==0:continue
   out[:,j]+=c*np.prod(points**np.array(powers),axis=1)
 return out
def main():
 assert not OUT.exists();start=time.time();r=F('0.71054833409295381132770417927279124');N=[]
 for k in range(7):
  p,c=features(r,k,7-k);cols=nullspace_two_rows(p,c)
  z=np.array([[float(v)for v in col]for col in cols]).T if cols else np.empty((7-k,0))
  N.append(np.linalg.qr(z,mode='reduced')[0]if cols else z)
 cand,G,old,ev=candidate_data(6);P,indices=polynomials(N)
 interior=cand[(1+2*np.prod(cand,axis=1)-np.sum(cand*cand,axis=1))>1e-7]
 A=np.vstack([evaluate(P,cand)]+[evaluate(P,interior,i)for i in range(3)])
 target=np.concatenate([np.sum((2-2*cand)**(-.5),axis=1)-ENERGY/12]+[(2-2*interior[:,i])**(-1.5)for i in range(3)])
 sol,_,rank,sv=np.linalg.lstsq(A,target,rcond=1e-10)
 U,S,Vh=np.linalg.svd(A,full_matrices=True);E=Vh[:rank];e=E@sol
 B={k:cp.Variable((n.shape[1],n.shape[1]),symmetric=True)for k,n in enumerate(N)if n.shape[1]}
 x=cp.hstack([B[k][i,j]for k,i,j in indices]);trace=sum(cp.trace(b)for b in B.values());eps=cp.Variable(nonneg=True)
 base=[b>>0 for b in B.values()]+[trace<=10000]
 settings=dict(solver='CLARABEL',tol_gap_abs=1e-9,tol_gap_rel=1e-9,tol_feas=1e-9,max_iter=200)
 def snapshot():return {'B':{str(k):b.value.tolist()for k,b in B.items()},'x':np.array(x.value).tolist(),'trace':float(trace.value),'min_eigenvalue':float(min(np.linalg.eigvalsh(b.value).min()for b in B.values())),'max_contact_error':float(abs(A@x.value-target).max())}
 prob=cp.Problem(cp.Minimize(eps+1e-13*trace),base+[cp.abs(A@x-target)<=eps]);prob.solve(**settings)
 result={'warning':'NONRIGOROUS, NOT proof or infeasibility certificate','degree':6,'conditional_domain':'Gram PSD intersect [-1,.57]^3, requires separately proved pair exclusion','trace_cap':10000,'nullities':[n.shape[1]for n in N],'exact_r_approximation':str(r),'projector_error_vs_eigenbasis':[float(np.linalg.norm(n@n.T-o@o.T))for n,o in zip(N,old)],'candidate_triangles':cand.tolist(),'interior_triangles':interior.tolist(),'equations':len(target),'unknowns':len(indices),'rank':int(rank),'singular_values':sv.tolist(),'linear_max_error':float(abs(A@sol-target).max()),'contact_rhs':'analytic f and f prime; no finite differences or minorant shift','feasibility_status':prob.status,'minimum_psd_equality_slack':float(eps.value)if eps.value is not None else None,'history':[]}
 if x.value is not None:result['minimum_slack_solution']=snapshot()
 def save():OUT.write_text(json.dumps(result,indent=2)+'\n')
 save();print(json.dumps({k:result[k]for k in ['feasibility_status','minimum_psd_equality_slack','linear_max_error','projector_error_vs_eigenbasis']}),flush=True)
 prob=cp.Problem(cp.Minimize(trace),base+[E@x==e]);prob.solve(**settings)
 result['exact_equality_status']=prob.status
 if x.value is not None:result['exact_equality_solution']=snapshot()
 save();print('PSD_EQUALITY',prob.status,result.get('exact_equality_solution',{}),flush=True)
 if x.value is None or result['exact_equality_solution']['max_contact_error']>1e-6:return
 rng=np.random.default_rng(607314);h,nodes,hcoef,hnodes=minorant();uv=rng.uniform(-1,1,(200,2))
 boundary=np.vstack([np.column_stack([uv,uv[:,0]*uv[:,1]+s*np.sqrt((1-uv[:,0]**2)*(1-uv[:,1]**2))])for s in (-1,1)])
 vertices=np.array([[.57,.57,.57],[-1,0,0],[-.5,-.5,-.5]])
 boundary=boundary[np.max(boundary,axis=1)<=LIMIT]
 cube=np.array(list(itertools.product(np.linspace(-1,LIMIT,7),repeat=3)));cube=cube[1+2*np.prod(cube,axis=1)-np.sum(cube*cube,axis=1)>=-1e-12]
 points=np.vstack([conditional_samples(1600,rng),boundary,cube,cand,vertices]);tau=cp.Variable(nonneg=True)
 for iteration in range(3):
  D=evaluate(P,points);rhs=np.sum(h(points),axis=1)-ENERGY/12
  prob=cp.Problem(cp.Minimize(tau+1e-12*trace),base+[E@x==e,D@x<=rhs+tau]);prob.solve(**settings)
  row={'iteration':iteration,'status':prob.status,'training_count':len(points)}
  if x.value is None:result['history'].append(row);save();break
  ss=snapshot();xx=np.array(x.value);row.update({k:ss[k]for k in ['trace','min_eigenvalue','max_contact_error']});row['tau']=float(tau.value)
  AA=[N[k]@B[k].value@N[k].T if k in B else np.zeros((7-k,7-k))for k in range(7)];cc=(ENERGY+1.5*AA[0].sum())/12
  def residual(p):return np.sum(h(p),axis=1)-cc-sum(np.einsum('nij,ij->n',m,a)for m,a in zip(design(p,6),AA))
  tests=conditional_samples(30000,rng);rr=residual(tests);ii=np.argsort(rr)[:80];w=tests[ii[0]]
  row['random_minimum']=float(rr.min());row['vertex_residuals']=residual(vertices).tolist()
  row['polynomial_numeric_design_max_error']=float(abs((np.sum(h(tests[:25]),axis=1)-ENERGY/12-evaluate(P,tests[:25])@xx)-residual(tests[:25])).max())
  angle=np.arccos(np.clip((w[2]-w[0]*w[1])/np.sqrt(max(1e-30,(1-w[0]**2)*(1-w[1]**2))),-1,1))
  seeds=[np.array([w[0],w[1],angle]),np.array([LIMIT,LIMIT,1.0])];des=[];additions=[tests[ii]]
  def fun(v):
   vv=np.asarray(v);single=vv.ndim==1
   if single:vv=vv[:,None]
   u,z,theta=vv;p=np.column_stack([u,z,u*z+np.sqrt(np.maximum(0,(1-u*u)*(1-z*z)))*np.cos(theta)])
   out=residual(p)+1e6*np.maximum(0,p[:,2]-LIMIT);return float(out[0])if single else out
  for si,seed in enumerate(seeds):
   opt=differential_evolution(fun,[(-1,LIMIT),(-1,LIMIT),(0,np.pi)],seed=901+iteration*2+si,x0=seed,popsize=12,maxiter=90,polish=True,vectorized=True,updating='deferred',tol=1e-8)
   triangle=from_angles(opt.x);feasible=bool(np.max(triangle)<=LIMIT+1e-12);des.append({'residual':float(residual(triangle)[0]),'penalized_objective':float(opt.fun),'domain_feasible':feasible,'triangle':triangle[0].tolist(),'angle_parameters':opt.x.tolist()});
   if feasible:additions.append(triangle)
  row['seeded_DE']=des;row['seconds']=time.time()-start;result['history'].append(row);result['solution']={**ss,'A':[a.tolist()for a in AA],'c':cc};result['nullspace_bases']=[n.tolist()for n in N];result['minorant_newton_coefficients']=hcoef.tolist();result['minorant_newton_nodes']=hnodes.tolist();save();print(json.dumps(row),flush=True)
  points=np.vstack([points,*additions])
 result['elapsed_seconds']=time.time()-start;save()
if __name__=='__main__':main()
