"""No SDP: deterministic Euclidean and relative-PSD contact-kernel patches."""
import time,json,itertools,hashlib,signal
import numpy as np
from scipy.optimize import minimize
import d10_nearest_repair2026_resume_driver as m
ROOT=m.ROOT;PREFIX='d10_relative_patch2026_'
def main():
 start=time.time();b=m.fastbuild();N=b['N'];ind=b['indices'];comp=b['comp'];C=b['augA'];Z=b['augZ'];prepared=json.loads((ROOT/'d10_nearest_repair2026_results.json').read_text());rawref=np.array(prepared['seed_x']);ref=b['augsol']+Z@(Z.T@(rawref-b['augsol']));BB,AA,c=m.original(ref,N,ind);gQ=-comp.design(m.Q[None])[0];rq=float(comp.kernel(ref)(m.Q)[0]);delta=1e-9-rq;grad=Z@(Z.T@gQ);eu=delta*grad/(grad@grad)
 out={'warning':'numerical linear algebra only; no SDP/no exact certificate','diagnostic':b['diagnostic'],'seed_x':ref.tolist(),'seed_raw_x':rawref.tolist(),'seed_Q_R':rq,'Q_delta_target':delta,'euclidean_projected_gradient_norm':float(np.linalg.norm(grad)),'euclidean_dx_norm':float(np.linalg.norm(eu)),'history':[],'sources':{name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest()for name in ['d10_sharpconvex2026_center_results.json','d10_nearest_repair2026_results.json','d10_nearest_repair2026_resume_driver.py']}};path=ROOT/(PREFIX+'results.json');assert not path.exists()
 def save():path.write_text(json.dumps(out,indent=2)+'\n')
 save();rng=np.random.default_rng(20270103);mandatory=np.array(prepared['mandatory_points']);curve=np.array(prepared['curve']);points=m.clean(np.vstack([m.random_cond(10000,rng),m.boundary_points(2000,rng),mandatory]));contact=np.array(prepared['full_contact_set']);T=np.zeros((len(ind),len(ind)));index={t:j for j,t in enumerate(ind)};col=0
 for k,block in BB.items():
  k=int(k);L=np.linalg.cholesky(block);n=len(block)
  for i in range(n):
   for j in range(i,n):
    Y=np.zeros((n,n));Y[i,j]=Y[j,i]=1 if i==j else 1/np.sqrt(2);D=L@Y@L.T
    for a in range(n):
     for q in range(a,n):T[index[k,a,q],col]=D[a,q]
    col+=1
 CT=C@T;_,sv,vh=np.linalg.svd(CT,full_matrices=True);rank=int(sum(sv>sv[0]*1e-10));ZR=vh[rank:].T;W=T@ZR;out['relative_rank']=rank;out['relative_singular_values']=sv.tolist();out['relative_null_error']=float(abs(C@W).max());out['T']=T.tolist();out['Zrel']=ZR.tolist();out['N']=[n.tolist()for n in N];out['indices']=[list(t)for t in ind];save();print('BUILD',time.time()-start,'rank',rank,'eu_dx',np.linalg.norm(eu),flush=True)
 constraints=[m.Q];targets=[1e-9];mode='Euclidean';x=ref+eu
 for iteration in range(3):
  if time.time()-start>150:out['stop_reason']='180second guard';break
  bb,aa,cc=m.original(x,N,ind);actual=m.IndependentActual(aa,cc);kernel=comp.kernel(x);vv=kernel(points);ix=np.argsort(vv)[:64];av=actual(points[ix]);rows=[{'point':p.tolist(),'R':float(v),'kind':'compiled_scan_originalA_check'}for p,v in zip(points[ix],av)];seeds=[m.Q]+[points[i]for i in ix[:8]]+list(curve[::10]);valstart=time.time()
  def alarm(*args):raise TimeoutError()
  signal.signal(signal.SIGALRM,alarm);signal.setitimer(signal.ITIMER_REAL,13)
  try:
   def fg(p):
    v,g=actual(p,True);return float(v[0]),g[0]
   for seed in seeds:
    if time.time()-valstart>11:break
    op=minimize(fg,seed,jac=True,method='SLSQP',bounds=[(-1,.56)]*3,constraints=[{'type':'ineq','fun':lambda z:m.gram(z)[0]}],options={'maxiter':80,'ftol':1e-14});q=op.x
    if min(q)>=-1 and max(q)<=.56 and m.gram(q)[0]>=-1e-12:rows.append({'point':q.tolist(),'R':float(actual(q)[0]),'kind':'independent_originalA_local','success':bool(op.success)})
  except TimeoutError:pass
  finally:signal.setitimer(signal.ITIMER_REAL,0)
  rows.sort(key=lambda t:t['R']);checks=np.array([t['point']for t in rows]);checked=actual(checks);gg,hh=m.jets(x,comp,b['cand']);bd=[]
  for j in np.flatnonzero(b['boundary']):
   g,Hg,tan=m.gram_geometry(b['cand'][j]);lam=float(g@gg[j]/(g@g));bd.append({'index':int(j),'lambda':lam,'tangent_error':float(np.linalg.norm(tan.T@gg[j])),'corrected_eigs':np.linalg.eigvalsh(tan.T@(hh[j]-lam*Hg)@tan).tolist()})
  row={'iteration':iteration,'mode':mode,'dx_norm':float(np.linalg.norm(x-ref)),'minB':float(min(np.linalg.eigvalsh(v).min()for v in bb.values())),'trace':float(sum(np.trace(v)for v in bb.values())),'contact_error':float(max(abs(C@x-b['augb']))),'interior_Hmin':float(np.linalg.eigvalsh(hh[b['interior']]).min()),'boundary':bd,'Q_R':float(actual(m.Q)[0]),'P_R':float(actual(m.P)[0]),'minimum_originalA':float(checked.min()),'originalA_compiled_error':float(max(abs(checked-kernel(checks)))),'worst_points':rows,'solution':{'x':x.tolist(),'B':{k:v.tolist()for k,v in bb.items()},'A':[a.tolist()for a in aa],'N':[n.tolist()for n in N],'c':cc},'elapsed_seconds':time.time()-start}
  if mode=='relative':row.update(relative_y_norm=float(np.linalg.norm(y)),relative_norm_bound_PSD=bool(np.linalg.norm(y)<1),active_subset=list(active),active_multipliers=mult.tolist())
  scan=ROOT/(PREFIX+f'scan_{iteration}.npz');np.savez_compressed(scan,points=points,compiled_R=vv,verified_points=checks,originalA_R=checked);out['history'].append(row);out['solution']=row['solution'];save();print('PATCH',iteration,mode,'minR',row['minimum_originalA'],'minB',row['minB'],'dx',row['dx_norm'],'seconds',time.time()-start,flush=True)
  if row['minB']>0 and row['minimum_originalA']>=-5e-12:out['stop_reason']='finite validation threshold reached';break
  if mode=='relative' or row['minB']>0:
   p=np.array(rows[0]['point']);p=(1-1e-7)*p if m.gram(p)[0]<0 else p
   if float(actual(p)[0])< -5e-12:constraints.append(p);targets.append(1e-9)
  G=-comp.design(np.array(constraints))@W;need=np.array(targets)-comp.kernel(ref)(np.array(constraints));best=None
  for nactive in range(1,len(constraints)+1):
   for subset in itertools.combinations(range(len(constraints)),nactive):
    H=G[list(subset)];mul=np.linalg.lstsq(H@H.T,need[list(subset)],rcond=1e-12)[0];yy=H.T@mul
    if min(mul)>=-1e-8 and np.min(G@yy-need)>=-1e-12 and(best is None or yy@yy<best[0]):best=(yy@yy,yy,subset,mul)
  if best is None:out['stop_reason']='small active set no feasible numerical candidate';break
  _,y,active,mult=best;x=ref+W@y;mode='relative'
 out.setdefault('stop_reason','three deterministic patches exhausted');out['elapsed_seconds']=time.time()-start;save();print('FINAL',out['stop_reason'],out['elapsed_seconds'],flush=True)
if __name__=='__main__':main()
