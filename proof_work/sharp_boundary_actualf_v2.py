"""NONRIGOROUS targeted Gram-boundary cutting planes; never a proof.
Run PYTHONPATH=proof_work:proof_work/python_deps OPENBLAS_NUM_THREADS=1 python3 ...
New .56 domain relies on parent's independent pair056_optimized_certificate.json.
"""
import argparse,json,itertools,time,warnings
from pathlib import Path
from fractions import Fraction as F
import numpy as np
import cvxpy as cp
from scipy.optimize import minimize,differential_evolution
from scipy.sparse import csr_matrix
from candidate_low_rank import features,nullspace_two_rows
from certify_three_point_d4 import const,add,scale,mul,mono,permute,diag
from sharp_three_point import candidate_data,ENERGY
from sharp_d8_conditional_actualf_eliminated import evaluate
from three_point_sampled import design,sample_triangles
LIMIT=.56
ANGLE=float(np.arccos(LIMIT))
ROOT=Path(__file__).parent
SEED=261016853

def polynomials(N,degree):
 u,v,t=(mono(i,1)for i in range(3));a=add(t,scale(mul(u,v),-1));b=mul(add(const(1),scale(mul(u,u),-1)),add(const(1),scale(mul(v,v),-1)))
 Q=[const(1),a]
 for k in range(1,degree):Q.append(add(scale(mul(a,Q[-1]),2),scale(mul(b,Q[-2]),-1)))
 raw=[]
 for k in range(degree+1):
  block=[]
  for i in range(degree+1-k):
   row=[]
   for j in range(degree+1-k):
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

class Compiled:
 def __init__(self,P):
  self.powers=np.array(sorted(set(itertools.chain.from_iterable(p.keys()for p in P))),dtype=int);self.mp=int(self.powers.max())
  lookup={tuple(e):i for i,e in enumerate(self.powers)};rr=[];cc=[];vv=[]
  for j,p in enumerate(P):
   for e,v in p.items():rr.append(lookup[e]);cc.append(j);vv.append(float(v))
  self.M=csr_matrix((vv,(rr,cc)),shape=(len(self.powers),len(P)))
 def monomials(self,pts,powers=None):
  pts=np.atleast_2d(pts);pw=self.powers if powers is None else powers
  tab=pts[:,:,None]**np.arange(self.mp+1)
  return tab[:,0,pw[:,0]]*tab[:,1,pw[:,1]]*tab[:,2,pw[:,2]]
 def design(self,pts):
  pts=np.atleast_2d(pts)
  return np.vstack([self.M.T.dot(self.monomials(pts[i:i+1000]).T).T for i in range(0,len(pts),1000)])
 def kernel(self,xx):
  co=np.asarray(self.M@xx);der=[]
  for axis in range(3):
   power=self.powers.copy();coef=co*power[:,axis];power[:,axis]=np.maximum(0,power[:,axis]-1);der.append((power,coef))
  def residual(pts,grad=False):
   pts=np.atleast_2d(pts);value=np.sum((2-2*pts)**(-.5),axis=1)-ENERGY/12-self.monomials(pts)@co
   if not grad:return value
   g=(2-2*pts)**(-1.5)
   for axis,(power,coef)in enumerate(der):g[:,axis]-=self.monomials(pts,power)@coef
   return value,g
  return residual

def valid(points):
 a=np.atleast_2d(points);return (np.max(a,axis=1)<=LIMIT+2e-12)&(np.min(a,axis=1)>=-1-2e-12)&(1+2*np.prod(a,axis=1)-np.sum(a*a,axis=1)>=-2e-11)
def dedup(points):
 a=np.sort(np.atleast_2d(points),axis=1);a=a[valid(a)];return np.unique(np.round(a,13),axis=0)
def random_cond(count,rng):
 batches=[];n=0
 while n<count:
  a=sample_triangles(max(count,1000),rng);a=a[valid(a)];batches.append(a);n+=len(a)
 return np.vstack(batches)[:count]
def map_angles(v,sign=None,jac=False):
 v=np.atleast_2d(v);a,b=v[:,0],v[:,1];ca,cb=np.cos(a),np.cos(b);sa,sb=np.sin(a),np.sin(b)
 if sign is None:th=v[:,2];ct,st=np.cos(th),np.sin(th)
 else:ct=sign;st=0
 pts=np.column_stack([ca,cb,ca*cb+sa*sb*ct])
 if not jac:return pts
 J=np.zeros((len(v),3,3 if sign is None else 2));J[:,0,0]=-sa;J[:,1,1]=-sb;J[:,2,0]=-sa*cb+ca*sb*ct;J[:,2,1]=-ca*sb+sa*cb*ct
 if sign is None:J[:,2,2]=-sa*sb*st
 return pts,J

def boundary_points(count,rng):
 out=[]
 while sum(len(a)for a in out)<count:
  ab=rng.uniform(ANGLE,np.pi,(max(100,count),2))
  for sign in (-1,1):
   p=map_angles(ab,sign);p=p[valid(p)];out.append(p)
 return np.vstack(out)[:count]
def near_points(count,rng):
 out=[]
 while sum(len(a)for a in out)<count:
  u=-1+10**rng.uniform(-13,-1,max(count,100));v=rng.uniform(-LIMIT,LIMIT,len(u));th=rng.uniform(0,np.pi,len(u));t=u*v+np.sqrt((1-u*u)*(1-v*v))*np.cos(th)
  p=np.column_stack([u,v,t]);out.append(p[valid(p)])
 return np.vstack(out)[:count]
def angle_of(p):
 u,v,t=p;return np.array([np.arccos(np.clip(u,-1,1)),np.arccos(np.clip(v,-1,1)),np.arccos(np.clip((t-u*v)/np.sqrt(max(1e-30,(1-u*u)*(1-v*v))),-1,1))])

def validate(comp,xx,rng,iteration,degree):
 residual=comp.kernel(xx);additions=[];rows={};all_found=[]
 def record(kind,p):
  p=np.asarray(p).ravel();ok=bool(valid(p)[0]);val=float(residual(p)[0]);d={'kind':kind,'residual':val,'triangle':p.tolist(),'domain_feasible':ok,'gram_determinant':float(1+2*np.prod(p)-p@p)}
  if ok:all_found.append(d);additions.append(p[None])
  return d
 random=random_cond(18000,rng);boundary=boundary_points(12000,rng);near=near_points(8000,rng)
 for name,pts in [('random',random),('boundary_random',boundary),('near_antipodal',near)]:
  vals=residual(pts);ii=np.argsort(vals)[:90];rows[name+'_minimum']=float(vals[ii[0]]);rows[name+'_worst']=record(name,pts[ii[0]]);additions.append(pts[ii])
 vertices=np.array([[-1,0,0],[-1,-LIMIT,LIMIT],[-1,LIMIT,-LIMIT],[-.5,-.5,-.5],[LIMIT,LIMIT,2*LIMIT**2-1]])
 rows['vertices']=[record('vertex',p)for p in vertices]
 # Independent 2D optimization on each linear component of Gram boundary.
 boundaries=[]
 for sign,component in [(-1,0),(1,1),(1,-1)]:
  if sign==-1:
   cf=lambda ab:2*np.pi-ANGLE-ab[0]-ab[1];cj=lambda ab:np.array([-1.,-1.])
  else:
   cf=lambda ab,c=component:c*(ab[0]-ab[1])-ANGLE;cj=lambda ab,c=component:np.array([c,-c],dtype=float)
  def objective(ab):
   pts,J=map_angles(ab,sign,True);val,g=residual(pts,True);return float(val[0]),g[0]@J[0]
  seeds=[]
  for p in boundary[np.argsort(residual(boundary))[:20]]:
   ab=np.arccos(np.clip(p[:2],-1,1))
   if cf(ab)>=-1e-10:seeds.append(ab)
  while len(seeds)<12:
   ab=rng.uniform(ANGLE,np.pi,2)
   if cf(ab)>=0:seeds.append(ab)
  best=None
  for ab in seeds[:16]:
   opt=minimize(objective,ab,jac=True,method='SLSQP',bounds=[(ANGLE,np.pi)]*2,constraints=[{'type':'ineq','fun':cf,'jac':cj}],options={'maxiter':120,'ftol':1e-12})
   p=map_angles(opt.x,sign)[0]
   if valid(p)[0]:
    d=record('boundary_local_'+str((sign,component)),p)
    if best is None or d['residual']<best['residual']:best=d
  def fun(v):
   v=np.asarray(v);single=v.ndim==1;vv=v[None]if single else v.T
   vals=residual(map_angles(vv,sign))+1e3*np.maximum(0,np.array([-cf(q)for q in vv]))
   return float(vals[0])if single else vals
  de=differential_evolution(fun,[(ANGLE,np.pi)]*2,seed=SEED+degree*20+iteration*7+component,popsize=12,maxiter=90,polish=True,vectorized=True,updating='deferred',tol=1e-9)
  dp=map_angles(de.x,sign)[0];dd=record('boundary_DE_'+str((sign,component)),dp)
  boundaries.append({'sign':sign,'component':component,'local_best':best,'DE':dd,'DE_penalized':float(de.fun)})
 rows['boundary_2D']=boundaries
 # Interior SLSQP, including seeds close to Gram boundary and antipodal lines.
 tests=np.vstack([random,boundary,near]);vals=residual(tests);seeds=[angle_of(p)for p in tests[np.argsort(vals)[:18]]]
 seeds.extend(rng.uniform([ANGLE,ANGLE,0],[np.pi,np.pi,np.pi],(8,3)))
 local=[]
 def obj(v):
  p,J=map_angles(v,None,True);value,g=residual(p,True);return float(value[0]),g[0]@J[0]
 def cf3(v):return float(LIMIT-map_angles(v)[0,2])
 def cj3(v):return -map_angles(v,None,True)[1][0,2]
 for seed in seeds:
  opt=minimize(obj,seed,jac=True,method='SLSQP',bounds=[(ANGLE,np.pi),(ANGLE,np.pi),(0,np.pi)],constraints=[{'type':'ineq','fun':cf3,'jac':cj3}],options={'maxiter':140,'ftol':1e-12})
  if valid(map_angles(opt.x))[0]:local.append(record('interior_local',map_angles(opt.x)[0]))
 rows['local_3D_best']=min(local,key=lambda a:a['residual'])if local else None
 # Seeded DE is only one validator, not the sole search.
 def defun(v):
  v=np.asarray(v);single=v.ndim==1;vv=v[None]if single else v.T;p=map_angles(vv);vals=residual(p)+1e3*np.maximum(0,p[:,2]-LIMIT)
  return float(vals[0])if single else vals
 des=[]
 for si in range(2):
  seed=seeds[si];opt=differential_evolution(defun,[(ANGLE,np.pi),(ANGLE,np.pi),(0,np.pi)],seed=SEED+iteration*11+si+degree,popsize=12,maxiter=100,polish=True,vectorized=True,updating='deferred',x0=seed,tol=1e-9)
  dd=record('seeded_DE3',map_angles(opt.x)[0]);dd['penalized_objective']=float(opt.fun);des.append(dd)
 rows['seeded_DE_3D']=des
 rows['independent_minimum']=min(d['residual']for d in all_found);rows['worst_points']=sorted(all_found,key=lambda a:a['residual'])[:15]
 # Check our compiled polynomial calculation against the original, independent kernel design.
 return rows,dedup(np.vstack(additions))

def run(degree,rounds,out):
 assert not out.exists();start=time.time();rng=np.random.default_rng(SEED+degree);r=F('0.71054833409295381132770417927279124');N=[]
 for k in range(degree+1):
  p,c=features(r,k,degree+1-k);cols=nullspace_two_rows(p,c);z=np.array([[float(v)for v in col]for col in cols]).T if cols else np.empty((degree+1-k,0));N.append(np.linalg.qr(z,mode='reduced')[0]if cols else z)
 cand,G,old,eigen=candidate_data(degree);P,indices=polynomials(N,degree);comp=Compiled(P)
 interior=cand[(1+2*np.prod(cand,axis=1)-np.sum(cand*cand,axis=1))>1e-7]
 Aeq=np.vstack([evaluate(P,cand)]+[evaluate(P,interior,i)for i in range(3)])
 target=np.concatenate([np.sum((2-2*cand)**(-.5),axis=1)-ENERGY/12]+[(2-2*interior[:,i])**(-1.5)for i in range(3)])
 sol,_,rank,sv=np.linalg.lstsq(Aeq,target,rcond=1e-10);_,_,Vh=np.linalg.svd(Aeq,full_matrices=True);Z=Vh[rank:].T
 free=cp.Variable(Z.shape[1]);x=sol+Z@free;index={t:j for j,t in enumerate(indices)};B={}
 for k,n in enumerate(N):
  if n.shape[1]:B[k]=cp.bmat([[x[index[k,min(i,j),max(i,j)]]for j in range(n.shape[1])]for i in range(n.shape[1])])
 trace=sum(cp.trace(b)for b in B.values());tau=cp.Variable(nonneg=True);base=[b>>0 for b in B.values()]+[trace<=1e5]
 oldfile=ROOT/'sharp_d8_conditional_actualf_eliminated.json';previous=json.loads(oldfile.read_text());oldx=np.array(previous['solution']['x'])
 if degree==8:free.value=Z.T@(oldx-sol)
 else:
  # Lift old monomial A blocks into the larger exact-feature QR subspaces.
  oldA=[np.array(a)for a in previous['solution']['A']];lift=[]
  for k,n in enumerate(N):
   aa=np.zeros((degree+1-k,degree+1-k))
   if k<len(oldA):aa[:oldA[k].shape[0],:oldA[k].shape[1]]=oldA[k]
   lift.append(n.T@aa@n)
  lifted=np.array([lift[k][i,j]for k,i,j in indices]);free.value=Z.T@(lifted-sol)
 oldpoints=[]
 for row in previous['history']:
  for dd in row.get('seeded_DE',[]):oldpoints.append(dd['triangle'])
 oldpoints.extend([[.4654922366,.2188732080,-.7617086021],[-.2154064377,.2078907056,.2078902869],[-1,0,0]])
 nearline=np.array([[-1,v,-v]for v in np.linspace(-LIMIT,LIMIT,81)])
 points=dedup(np.vstack([random_cond(950,rng),boundary_points(1300,rng),near_points(700,rng),nearline,cand,oldpoints]))
 result={'warning':'NONRIGOROUS numerical candidate search, NOT proof or infeasibility certificate','degree':degree,'domain':'Gram PSD intersection [-1,.56]^3','pair_exclusion_dependency':'pair056_optimized_certificate.json','trace_cap':1e5,'regularizer':'objective=1000*tau+1e-8*trace (equiv tau+1e-11*trace)','seed':SEED+degree,'equations':len(target),'unknowns':len(indices),'rank':int(rank),'nullities':[n.shape[1]for n in N],'singular_values':sv.tolist(),'contact_linear_max_error':float(abs(Aeq@sol-target).max()),'warmstart_from':str(oldfile),'history':[],'rhs':'actual Coulomb f, analytic f prime; no polynomial minorant','nullspace_bases':[n.tolist()for n in N],'initial_training_points':points.tolist()}
 def save():out.write_text(json.dumps(result,indent=2)+'\n')
 save();print('INITIAL',degree,len(points),len(indices),rank,'build_seconds',time.time()-start,flush=True)
 settings=dict(solver='CLARABEL',tol_gap_abs=2e-8,tol_gap_rel=2e-8,tol_feas=2e-9,max_iter=400)
 for iteration in range(rounds):
  D=comp.design(points);rhs=np.sum((2-2*points)**(-.5),axis=1)-ENERGY/12
  prob=cp.Problem(cp.Minimize(1000*tau+1e-8*trace),base+[D@x<=rhs+tau]);errors=[];solver='CLARABEL'
  try:prob.solve(**settings,warm_start=True)
  except cp.error.SolverError as er:
   errors.append(repr(er));print('CLARABEL retry loose',flush=True)
   try:prob.solve(solver='CLARABEL',tol_gap_abs=1e-6,tol_gap_rel=1e-6,tol_feas=2e-8,max_iter=500,warm_start=True)
   except cp.error.SolverError as er:
    errors.append(repr(er));solver='SCS';print('SCS fallback',flush=True);prob.solve(solver='SCS',eps=3e-7,max_iters=15000,warm_start=True)
  row={'iteration':iteration,'training_count':len(points),'status':prob.status,'solver':solver,'solver_errors':errors,'seconds_at_solve':time.time()-start}
  if x.value is None:result['history'].append(row);save();break
  xx=np.asarray(x.value).ravel();bb={str(k):np.asarray(b.value)for k,b in B.items()};AA=[N[k]@bb[str(k)]@N[k].T if str(k)in bb else np.zeros((degree+1-k,degree+1-k))for k in range(degree+1)];cc=(ENERGY+1.5*AA[0].sum())/12
  row.update({'tau':float(tau.value),'trace':float(trace.value),'min_eigenvalue':float(min(np.linalg.eigvalsh(b).min()for b in bb.values())),'contact_max_error':float(abs(Aeq@xx-target).max()),'training_min_residual':float(np.min(rhs-D@xx))})
  val,additions=validate(comp,xx,rng,iteration,degree);row.update(val)
  cross=random_cond(40,rng);original=np.sum((2-2*cross)**(-.5),axis=1)-cc-sum(np.einsum('nij,ij->n',m,a)for m,a in zip(design(cross,degree),AA));row['independent_design_discrepancy']=float(abs(original-comp.kernel(xx)(cross)).max())
  row['seconds']=time.time()-start;result['history'].append(row);result['solution']={'x':xx.tolist(),'B':{k:b.tolist()for k,b in bb.items()},'A':[a.tolist()for a in AA],'c':cc};result['training_points']=points.tolist();save()
  print(json.dumps({k:row[k]for k in ['iteration','training_count','tau','trace','min_eigenvalue','contact_max_error','independent_minimum','independent_design_discrepancy','seconds']}),flush=True);print('WORST',row['worst_points'][:3],flush=True)
  if row['tau']<1e-7 and row['independent_minimum']>-2e-7:result['stop_reason']='nearzero candidate; prioritize certification review';save();break
  if degree==8 and iteration>=4:
   last=[h['tau']for h in result['history'][-3:]]
   if min(last)>1e-4 and max(last)-min(last)<max(2e-5,.06*max(last)):
    result['stop_reason']='after>=5 rounds, last3 tau stable >1e-4; permit bounded d10';result['stable_positive_tau']=True;save();break
  points=dedup(np.vstack([points,additions]))
 result['elapsed_seconds']=time.time()-start;save();return result

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--degree',type=int,default=8);ap.add_argument('--rounds',type=int,default=10);ap.add_argument('--out',required=True);args=ap.parse_args();run(args.degree,args.rounds,Path(args.out))
if __name__=='__main__':main()
