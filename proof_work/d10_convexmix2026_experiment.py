"""Finite PSD convex mixture proposal search; global positivity unproved."""
import time,json,itertools,hashlib,ast,signal
from pathlib import Path
START=time.monotonic()
import numpy as np
from fractions import Fraction as Fr
from scipy.optimize import minimize,differential_evolution,NonlinearConstraint
from certify_three_point_d4 import const,add,scale,mul,mono,permute,diag,ldl
from sharp_boundary_actualf_v3 import Compiled,random_cond,boundary_points,valid
from d12_contact2026_core import exact_candidate,RSTRING
ROOT=Path(__file__).parent;PREFIX='d10_convexmix2026_';OUT=ROOT/(PREFIX+'results.json');assert not OUT.exists()
class Budget(Exception):pass
signal.signal(signal.SIGALRM,lambda *unused:(_ for _ in ()).throw(Budget('75second hard budget')));signal.alarm(74)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
paths=[ROOT/'nonsharp_d10_root25_7599205_v10.json',ROOT/'sharp_contact_refinement2026_results.json',ROOT/'conditional_h27_certificate.json',ROOT/'negative_valley_seed1_2026_summary.json']
old=json.loads(paths[0].read_text());sd=json.loads(paths[1].read_text());seed=sd['best_solution'];assert seed['iteration']==2;assert abs(seed['trace']-660.6648846376025)<1e-8;assert seed['min_B_eigenvalue']>2e-6
oldA=[[[Fr(z)for z in row]for row in a]for a in old['A']];H=[Fr(z)for z in old['h_monomial']];B0=Fr(old['target']);E=Fr('25.75998653126983156');Bseed=E-Fr('1e-8')
Ao=[np.array([[float(z)for z in row]for row in a])for a in oldA];rawA=[np.array(a)for a in seed['A']]
seedA=None;seedpiv=None
for eps in [Fr('1e-11'),Fr('1e-10')]:
 q=[[[Fr(int(round(float((a[i,j]+a[j,i])/2)*10**14)),10**14)+eps*(i==j)for j in range(len(a))]for i in range(len(a))]for a in rawA]
 try:sp=[ldl(a)for a in q];seedA=q;seedpiv=sp;break
 except AssertionError:pass
result={'warning':'PROPOSAL ONLY; no global nonnegativity or strict bound claim','source_sha256':{str(p):sha(p)for p in paths},'seed_iteration':2,'seed_trace':seed['trace'],'seed_min_reduced_eigenvalue':seed['min_B_eigenvalue'],'seed_original_min_eigenvalue':float(min(np.linalg.eigvalsh(a).min()for a in rawA)),'seed_quantization':'symmetric 1e-14, diagonal shift at most1e-10','seed_diagonal_shift':str(eps),'seed_fraction_LDL_passed':seedA is not None,'domain':'full Gram PSD intersection [-1,.56]^3, no extra budget constraints','history':[],'proposal':None}
def save():OUT.write_text(json.dumps(result,indent=2)+'\n')
save()
if seedA is None:result['stop_reason']='seed quantization failed strict Fraction LDL';save();raise SystemExit()
# Reuse exporter polynomial normalization verbatim.
u,v,t=(mono(i,1)for i in range(3));a=add(t,scale(mul(u,v),-1));b=mul(add(const(1),scale(mul(u,u),-1)),add(const(1),scale(mul(v,v),-1)));Q=[const(1),a]
for k in range(1,10):Q.append(add(scale(mul(a,Q[-1]),2),scale(mul(b,Q[-2]),-1)))
def buildF(A):
 kernel={}
 for k in range(11):
  for i in range(11-k):
   for j in range(11-k):kernel=add(kernel,scale(mul(mul(mono(0,i),mono(1,j)),Q[k]),A[k][i][j]))
 return scale(add(*(permute(kernel,pm)for pm in itertools.permutations(range(3)))),Fr(1,6))
Fo={tuple(k):Fr(z)for k,z in old['F_monomial']};Fs=buildF(seedA);cs=(Bseed+Fr(3,2)*sum(Fs.values()))/12
hp={(i,0,0):z for i,z in enumerate(H)if z};hs=add(*(permute(hp,pm)for pm in [(0,1,2),(1,0,2),(2,1,0)]))
def makeR(F,c):return add(hs,scale(F,-7),*(scale(diag(F,j),-1)for j in range(3)),const(-c))
Ro={tuple(k):Fr(z)for k,z in old['residual_monomial']};Rs=makeR(Fs,cs);comp=Compiled([Ro,Rs]);coeff=comp.M.toarray();pw=comp.powers
# Gradient coefficients retain the existing monomial evaluation convention.
der=[]
for ax in range(3):
 pp=pw.copy();dd=coeff*pp[:,ax,None];pp[:,ax]=np.maximum(0,pp[:,ax]-1);der.append((pp,dd))
def both(p):
 p=np.atleast_2d(p);return np.vstack([comp.monomials(p[j:j+700])@coeff for j in range(0,len(p),700)])
def evalmix(p,theta,shift,gradient=False):
 z=np.atleast_2d(p);w=np.array([1-theta,theta]);vv=both(z)@w+shift
 if not gradient:return vv
 return vv,np.column_stack([comp.monomials(z,pp)@(dd@w)for pp,dd in der])
rng=np.random.default_rng(2026101727);cand=np.array([[float(z)for z in p]for p in exact_candidate(Fr(RSTRING))[0]])
valleys=json.loads(paths[3].read_text());known=np.array([q['center_minimum_sample']for q in valleys['valleys'][:3]]+ [[-.296937,.422535,.422535],[.3727866847029806,.56,-.040144373353202034],[.56,.56,.56],[-1,0,0],[-1,-.56,.56]])
random=random_cond(50000,rng);boundary=boundary_points(10000,rng);pool=np.vstack([random,boundary,cand,known]);rv=both(pool);result['random_count']=len(random);result['boundary_count']=len(boundary);result['known_points']=known.tolist();result['build_and_pool_seconds']=time.monotonic()-START
print('BUILD',result['build_and_pool_seconds'],'seedLDL',str(eps),flush=True)
# Original six-permutation recurrence independently checks compiled normalization.
srcpath=ROOT/'sharp_contact_refinement2026_refine.py';tree=ast.parse(srcpath.read_text());node=next(n for n in tree.body if isinstance(n,ast.ClassDef)and n.name=='IndependentActual');ns={'np':np,'itertools':itertools,'DEGREE':10};exec(compile(ast.Module(body=[node],type_ignores=[]),str(srcpath),'exec'),ns)
def gram(p):z=np.atleast_2d(p);return 1+2*np.prod(z,axis=1)-np.sum(z*z,axis=1)
def gj(z):u,v,t=z;return np.array([2*(v*t-u),2*(u*t-v),2*(u*v-t)])
thetas=[(Fr(1,2),Fr('25.75995')),(Fr(1,4),Fr('25.759935'))]
try:
 for theta,target in thetas:
  if time.monotonic()-START>57:result['stop_reason']='remaining 75second budget insufficient';break
  th=float(theta);baseB=(1-theta)*B0+theta*Bseed;shift=float((baseB-target)/12);vv=rv@np.array([1-th,th])+shift;ii=np.argsort(vv);found=[(float(vv[q]),pool[q].copy(),'pool')for q in ii[:30]]
  locdeadline=min(time.monotonic()+3,START+62)
  for _,seedp,_ in found[:8]:
   if time.monotonic()>locdeadline:break
   def obj(z):
    if time.monotonic()>locdeadline:raise Budget()
    a,g=evalmix(z,th,shift,True);return float(a[0]),g[0]
   try:
    opt=minimize(obj,seedp,jac=True,method='SLSQP',bounds=[(-1,.56)]*3,constraints=[{'type':'ineq','fun':lambda z:float(gram(z)[0]),'jac':gj}],options={'maxiter':80,'ftol':1e-13})
    if valid(opt.x)[0]:found.append((float(evalmix(opt.x,th,shift)[0]),opt.x.copy(),'SLSQP'))
   except Budget:break
  de_start=time.monotonic();deadline=min(de_start+9,START+66);neval=0
  def decon(z):
   z=np.asarray(z);g=gram(z.reshape(3,-1).T);return float(g[0])if z.ndim==1 else g[None]
  def deobj(z):
   global neval
   if time.monotonic()>deadline:raise Budget()
   z=np.asarray(z);pp=z.reshape(3,-1).T;vv=evalmix(pp,th,shift);neval+=len(pp)
   if len(vv):q=int(vv.argmin());found.append((float(vv[q]),pp[q].copy(),'DE_evaluated'))
   return float(vv[0])if z.ndim==1 else vv
  init=random_cond(72,rng);init[:12]=cand
  try:opt=differential_evolution(deobj,[(-1,.56)]*3,constraints=[NonlinearConstraint(decon,0,np.inf)],init=init,maxiter=100000,tol=1e-10,polish=False,seed=20261017,vectorized=True,updating='deferred',callback=lambda x,convergence:time.monotonic()>deadline);destatus=str(opt.message)
  except Budget:destatus='time budget'
  found=sorted([z for z in found if valid(z[1])[0]],key=lambda z:z[0]);worst=found[0];Am=[[(1-theta)*x+theta*y for x,y in zip(ro,rs)]for ro,rs in []]if False else [[[(1-theta)*oldA[k][i][j]+theta*seedA[k][i][j]for j in range(11-k)]for i in range(11-k)]for k in range(11)]
  Fm=add(scale(Fo,1-theta),scale(Fs,theta));c=(target+Fr(3,2)*sum(Fm.values()))/12;Rf=makeR(Fm,c);Afloat=[np.array([[float(z)for z in ro]for ro in block])for block in Am];actual=ns['IndependentActual'](Afloat,float(c));check=np.vstack([pool[ii[:20]],np.array([z[1]for z in found[:30]]),random[:30]])
  # Convert actual Coulomb recurrence to the exact h27 minorant residual.
  ar=actual(check)+np.sum(np.polynomial.polynomial.polyval(check,np.array([float(z)for z in H]))-(2-2*check)**(-.5),axis=1);cr=evalmix(check,th,shift);k=int(ar.argmin());minR=float(ar[k])
  row={'theta':str(theta),'target':str(target),'random_min_R':float(vv[0])if False else float((rv[:50000]@np.array([1-th,th])+shift).min()),'random_negative_count':int(np.sum(rv[:50000]@np.array([1-th,th])+shift<0)),'boundary_min_R':float((rv[50000:60000]@np.array([1-th,th])+shift).min()),'pool_min_R':float((rv@np.array([1-th,th])+shift).min()),'observed_min_R_original_recurrence':minR,'worst_point':check[k].tolist(),'worst_gram':float(gram(check[k])[0]),'compiled_recurrence_difference':float(max(abs(ar-cr))),'DE_seconds':time.monotonic()-de_start,'DE_evaluations':neval,'DE_status':destatus,'known_R':evalmix(known,th,shift).tolist(),'seconds':time.monotonic()-START}
  result['history'].append(row);save();print('THETA',json.dumps(row),flush=True)
  if minR>1e-8:
   piv=[ldl(a)for a in Am]
   serialize=lambda p:[[list(k),str(z)]for k,z in sorted(p.items())]
   proposal={'status':'exact_components_prepared_global_positivity_UNPROVED','target':str(target),'source_model':'convex combination of unchanged rational old A and first PSD seed iteration2','theta':str(theta),'degree':10,'domain':'Gram PSD intersection [-1,14/25]^3','minorant_dependency':'conditional_h27_certificate.json','A':[[[str(z)for z in row]for row in a]for a in Am],'c':str(c),'F111':str(sum(Fm.values())),'h_monomial':[str(z)for z in H],'F_monomial':serialize(Fm),'d_monomial':serialize(diag(Fm,0)),'residual_monomial':serialize(Rf),'psd_exact_ldl_pivots':piv,'seed_psd_exact_ldl_pivots':seedpiv,'seed_rounding_denominator':'100000000000000','seed_added_diagonal_epsilon':str(eps),'source_sha256':result['source_sha256'],'normalization_exact':'12*c-3/2*F111=target; R=sum(h27)-7F-sum(diag F)-c','numeric_validation':row,'proof_status':'Fraction LDL positive; exact rational components. Global residual nonnegativity UNPROVED.'}
   assert 12*c-Fr(3,2)*sum(Fm.values())==target
   op=ROOT/(PREFIX+'proposal.json');assert not op.exists();op.write_text(json.dumps(proposal,indent=2)+'\n');result['proposal']=str(op);result['stop_reason']='positive numerical residual and exact PSD proposal exported';save();break
 result.setdefault('stop_reason','tested requested half and quarter; no positive feasible mixture')
except Budget as e:result['stop_reason']=str(e)
result['elapsed_seconds']=time.monotonic()-START;save();signal.alarm(0);print('FINAL',json.dumps({'elapsed_seconds':result['elapsed_seconds'],'stop_reason':result['stop_reason'],'proposal':result['proposal']}),flush=True)
