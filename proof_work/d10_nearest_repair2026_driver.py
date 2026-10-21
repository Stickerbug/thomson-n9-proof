"""New cone directions, normalized ridge positivity; numerical discovery only."""
import time,json,hashlib,itertools,signal
import numpy as np
import cvxpy as cp
from scipy.optimize import minimize,differential_evolution,NonlinearConstraint
from sharp_contact_refinement2026_core import *
from sharp_contact_refinement2026_refine import IndependentActual,solver_info
from sharp_boundary_actualf_v3 import random_cond,boundary_points
PREFIX='d10_nearest_repair2026_'
Q=np.array([-.7319927153030016,-.7319927162082746,.34931898965249153]);P=np.array([.56,.56,.56])
def gram(p):
 p=np.atleast_2d(p);return 1+2*np.prod(p,axis=1)-np.sum(p*p,axis=1)
def clean(p):
 p=np.atleast_2d(p);p=p[(p.min(axis=1)>=-1)&(p.max(axis=1)<=.56)&(gram(p)>=-2e-13)];_,ix=np.unique(np.round(p,13),axis=0,return_index=True);return p[np.sort(ix)]
def dist2(p,contacts):return np.min(np.sum((np.atleast_2d(p)[:,None,:]-contacts[None,:,:])**2,axis=2),axis=1)
def selected(pool,mandatory,res,contacts):
 mandatory=clean(mandatory);pool=clean(pool);keys={tuple(np.round(p,13)) for p in mandatory};remain=np.array([p for p in pool if tuple(np.round(p,13))not in keys]).reshape(-1,3);remain=remain[np.argsort(res(remain)/np.maximum(dist2(remain,contacts),1e-6))[:max(0,5000-len(mandatory))]];return clean(np.vstack([mandatory,remain]))
def validate(actual,comp,x,rng,curve,contacts,mandatory,iteration):
 start=time.time();rows=[];res=comp.kernel(x);pool=clean(np.vstack([random_cond(60000,rng),boundary_points(6000,rng),mandatory]));v=np.concatenate([res(pool[i:i+4000])for i in range(0,len(pool),4000)]);ix=np.argsort(v)[:64];original=actual(pool[ix]);np.savez_compressed(ROOT/(PREFIX+f"scan_{iteration}.npz"),points=pool,compiled_R=v,verified_points=pool[ix],originalA_R=original);v[ix]=original;rows.extend([{'point':p.tolist(),'R':float(a),'kind':'compiled_scan_originalA_check'}for p,a in zip(pool[ix],v[ix])]);seeds=[Q]+[pool[i] for i in ix[:10]]+list(curve[::10])+OLDPOINTS
 def alarm(*a):raise TimeoutError()
 signal.signal(signal.SIGALRM,alarm);signal.setitimer(signal.ITIMER_REAL,max(.1,24-time.time()+start))
 try:
  def fg(p):
   z,g=actual(p,True);return float(z[0]),g[0]
  for p in seeds:
   if time.time()-start>19:break
   op=minimize(fg,p,jac=True,method='SLSQP',bounds=[(-1,.56)]*3,constraints=[{'type':'ineq','fun':lambda z:gram(z)[0]}],options={'maxiter':90,'ftol':1e-14});z=op.x
   if gram(z)[0]>=-1e-12 and z.min()>=-1 and z.max()<=.56:rows.append({'point':z.tolist(),'R':float(actual(z)[0]),'kind':'independent_originalA_local','success':bool(op.success)})
  if time.time()-start<20:
   def con(z):
    z=np.asarray(z);single=z.ndim==1;p=z.reshape(3,-1).T;v=gram(p);return v[0] if single else v[None,:]
   de=differential_evolution(lambda z:float(res(z)[0])if np.ndim(z)==1 else res(z.T),[(-1,.56)]*3,constraints=[NonlinearConstraint(con,0,np.inf)],vectorized=True,updating='deferred',popsize=8,maxiter=35,polish=False,seed=202611+iteration);z=de.x
   if gram(z)[0]>=-1e-12:rows.append({'point':z.tolist(),'R':float(actual(z)[0]),'kind':'compiled_DE_originalA_check'})
 except TimeoutError:pass
 finally:signal.setitimer(signal.ITIMER_REAL,0)
 rows.sort(key=lambda z:z['R']);checks=np.array([z['point']for z in rows]);vv=actual(checks);return {'seconds':time.time()-start,'scan_size':len(pool),'worst_points':rows,'minimum_originalA':float(vv.min()),'compiled_original_error':float(np.max(abs(vv-res(checks))))},checks

def eigencuts(xx,b):
 gg,hh=jets(xx,b['comp'],b['cand']);out=[]
 for j,p in enumerate(b['cand']):
  if b['interior'][j]:directions=np.linalg.eigh(hh[j])[1].T
  else:
   g,Hg,T=gram_geometry(p);lam=g@gg[j]/(g@g);directions=(T@np.linalg.eigh(T.T@(hh[j]-lam*Hg)@T)[1]).T
  for v in directions:
   for radius in [1e-4,1e-3,.01]:
    for sign in [-1,1]:
     q=p+sign*radius*v
     if not b['interior'][j]:
      axis=int(np.argmax(abs(g)))
      for _ in range(6):
       dg=gram_geometry(q)[0][axis]
       if abs(dg)<1e-10:break
       q[axis]-=gram(q)[0]/dg
      q*=1-1e-13
     out.extend(itertools.permutations(q))
 return clean(np.array(out))
def run():
 start=time.time();rng=np.random.default_rng(20261117);b=build();N=b['N'];ind=b['indices'];comp=b['comp'];cand=b['cand'];contacts=np.unique(np.array([p for z in cand for p in itertools.permutations(z)]),axis=0);assert b['diagnostic']['contact_plus_tangent_max_error']<1e-8
 source=ROOT/'d10_sharpconvex2026_center_results.json';mix=json.loads(source.read_text())['weights_proposal'];old=json.loads((ROOT/'d10_ridge_repair2026_b2_results.json').read_text());global OLDPOINTS;OLDPOINTS=[np.array(w['point'])for row in old['history']for w in row['validation']['worst_points']];A0=list(map(np.array,mix['A']));B0=[n.T@a@n for n,a in zip(N,A0)];ref=np.array([B0[k][i,j]for k,i,j in ind]);sol=b['augsol'];Z=b['augZ'];ref_projected=sol+Z@(Z.T@(ref-sol));sol=ref_projected;Z=1e-4*Z;free=cp.Variable(Z.shape[1]);free.value=np.zeros(Z.shape[1]);x=sol+Z@free
 index={z:j for j,z in enumerate(ind)};B={k:cp.bmat([[x[index[k,min(i,j),max(i,j)]]for j in range(n.shape[1])]for i in range(n.shape[1])])for k,n in enumerate(N)if n.shape[1]};trace=sum(cp.trace(v)for v in B.values());constraints=[v>>1e-8*np.eye(v.shape[0])for v in B.values()]+[trace<=2000]
 for j,p in enumerate(cand):
  H=cp.bmat([[(float(3*(2-2*p[i])**(-2.5))if i==q else 0.)-derivative(comp,p[None],(i,q))[0]@x for q in range(3)]for i in range(3)])
  if b['interior'][j]:constraints.extend([H>>1e-6*np.eye(3),H>>2e-7*np.eye(3)])
  else:
   g,Hg,T=gram_geometry(p);lam=g@(b['fprime'][j]-b['Dr'][j]@x)/(g@g);constraints.extend([lam>=1e-8,T.T@H@T-lam*(T.T@Hg@T)>>1e-6*np.eye(2),T.T@H@T-lam*(T.T@Hg@T)>>2e-7*(T.T@T)])
 r=float(RSTRING);cgf=np.array([r*r/2-1,-r,r/2]);swap=cgf[[1,0,2]];curve=np.array([(1-t)*cgf+t*swap for t in np.linspace(0,1,81)]);lateral=np.vstack([curve+rng.normal(0,s,curve.shape)for s in [1e-4,1e-3,3e-3,1e-2]]);annuli=[]
 for radius in [1e-4,1e-3,1e-2,.03,.05]:
  for p in contacts:
   u=rng.normal(0,1,(5,3));u/=np.linalg.norm(u,axis=1)[:,None];annuli.append(p+radius*u)
 valleys=np.array([[-.759220762336624,-.29211600772137486,.32931701954562287],[.346480293,.346480553,.346480725],[-.071348864,.339279344,.339279344]])
 curve=np.array(old['curve']);initial_eigen=eigencuts(ref_projected,b);mandatory=clean(np.vstack([old['mandatory_points'],OLDPOINTS,initial_eigen]));pool=clean(np.vstack([old['initial_pool'],mandatory,random_cond(3500,rng),boundary_points(500,rng)]));points=selected(pool,mandatory,comp.kernel(ref),contacts)
 out=ROOT/(PREFIX+'results.json');assert not out.exists();result={'warning':'NUMERICAL DISCOVERY ONLY; no proof or cone infeasibility claim','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'diagnostic':b['diagnostic'],'seed_x':ref.tolist(),'N':[n.tolist()for n in N],'indices':[list(z)for z in ind],'full_contact_set':contacts.tolist(),'curve':curve.tolist(),'initial_pool':pool.tolist(),'mandatory_points':mandatory.tolist(),'history':[],'initial_eigencuts':initial_eigen.tolist(),'seed_projected':ref_projected.tolist(),'objective':'min sum_squares(z); x=oldref_projected+1e-4augZ@z; eta=1e-7 fixed','domain':'full Gram box[-1,.56]^3','build_seconds':time.time()-start};save=lambda:out.write_text(json.dumps(result,indent=2)+'\n');save();print('BUILD',len(points),'mandatory',len(mandatory),'seconds',time.time()-start,flush=True);assert time.time()-start<=70,'build70 cap'
 eta=1e-7;do_trace=False
 constraints.extend([1e6*(np.sum((2-2*Q)**(-.5))-ENERGY/12-comp.design(Q[None,:])[0]@x)>=1e-3,1e6*(np.sum((2-2*P)**(-.5))-ENERGY/12-comp.design(P[None,:])[0]@x)>=.1])
 for iteration in range(3):
  if time.time()-start>207:result['stop_reason']='total300 guard';break
  D=comp.design(points);rhs=np.sum((2-2*points)**(-.5),axis=1)-ENERGY/12;dd=dist2(points,contacts);scale=1/np.maximum(dd,1e-6);Dred=(D@Z)*scale[:,None];bred=(rhs-D@sol)*scale;con=constraints+[Dred@free+eta*(dd*scale)<=bred]
  prob=cp.Problem(cp.Minimize(cp.sum_squares(free)),con);err=None;st=time.time()
  try:prob.solve(solver='CLARABEL',time_limit=55,max_iter=250,tol_feas=1e-10,tol_gap_abs=1e-10,tol_gap_rel=1e-10,warm_start=True)
  except cp.error.SolverError as ex:err=repr(ex)
  row={'iteration':iteration,'mode':'min_distance','error':err,'solve_wall_seconds':time.time()-st,'cuts':points.tolist(),'solver':solver_info(prob)if prob.solver_stats else None}
  if x.value is None:row['no_iterate']=True;result['history'].append(row);result['stop_reason']='no iterate';save();break
  xx=np.asarray(x.value).ravel();bb,AA,c=original(xx,N,ind);gg,hh=jets(xx,comp,cand);actual=IndependentActual(AA,c);validation,additions=validate(actual,comp,xx,rng,curve,contacts,mandatory,iteration);row.update({'eta':eta,'z_squared_norm_objective':float(np.sum(np.asarray(free.value)**2)),'x_oldref_distance':float(np.linalg.norm(xx-ref)),'x_projectedref_distance':float(np.linalg.norm(xx-ref_projected)), 'affine_projection_error':float(np.linalg.norm(ref-ref_projected)),'trace':float(sum(np.trace(v)for v in bb.values())),'min_B_eigenvalue':float(min(np.linalg.eigvalsh(v).min()for v in bb.values())),'contact_error':float(np.max(abs(b['augA']@xx-b['augb']))),'interior_H_min':float(np.linalg.eigvalsh(hh[b['interior']]).min()),'training_minR':float(min(rhs-D@xx)),'validation':validation,'Q_R':float(actual(Q)[0]),'P_R':float(actual(P)[0]),'solution':{'x':xx.tolist(),'B':{k:v.tolist()for k,v in bb.items()},'A':[a.tolist()for a in AA],'N':[n.tolist()for n in N],'c':c}});row['boundary_jets']=[]
  for j in np.flatnonzero(b['boundary']):
   g,Hg,T=gram_geometry(cand[j]);lam=float(g@gg[j]/(g@g));row['boundary_jets'].append({'index':int(j),'lambda':lam,'tangent_error':float(np.linalg.norm(T.T@gg[j])),'tangent_H_eigenvalues':np.linalg.eigvalsh(T.T@(hh[j]-lam*Hg)@T).tolist()})
  result['history'].append(row);result['solution']=row['solution'];save();print('VALIDATED',iteration,json.dumps({k:v for k,v in row.items()if k not in ['cuts','solution','validation','boundary_jets']}),'minR',validation['minimum_originalA'],'seconds',time.time()-start,flush=True)
  if err or prob.status in ['infeasible','unbounded']:result['stop_reason']='finite model solver failure';break
  do_trace=False
  mandatory=clean(np.vstack([mandatory,additions,eigencuts(xx,b)]));pool=clean(np.vstack([pool,mandatory]));points=selected(pool,mandatory,comp.kernel(xx),contacts);result['mandatory_points']=mandatory.tolist()
 result.setdefault('stop_reason','authorized three rounds exhausted');result['elapsed_seconds']=time.time()-start;save();print('FINAL',result['stop_reason'],result['elapsed_seconds'],flush=True)
if __name__=='__main__':run()
