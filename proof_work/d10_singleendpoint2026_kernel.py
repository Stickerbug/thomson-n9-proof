if not __debug__:
 raise RuntimeError('Run certificate without -O')
"""Exact true-root contact correction and reduced-block positive definiteness."""
import itertools,json,time,argparse
import sympy as sp
from pathlib import Path
from fractions import Fraction as F
import numpy as np
from candidate_low_rank import features
from dyadic_interval import I,BITS,S
rootinfo=json.loads(Path(__file__).with_name('narrowroot2026_root.json').read_text());L,U=rootinfo['root_refined']
COLS=list(range(190))

def run(output,certificate=None,return_context=False,seed_input=None):
 rs=sp.symbols("r");field=sp.QQ.frac_field(rs)
 start=time.time();rr=I(L,U);r0=(F(L)+F(U))/2;NN=[];indices=[];pivots=[]
 for k in range(11):
  pf,cf=features(r0,k,11-k);p,c=features(rr,k,11-k);rows=[p[:],c[:]];fr=[pf[:],cf[:]];row=0;pivs=[]
  ps,cs=features(rs,k,11-k);ex=[[field.from_sympy(sp.cancel(v))for v in a]for a in [ps,cs]]
  for j in range(11-k):
   choice=next((i for i in range(row,2)if fr[i][j]),None)
   echoice=next((i for i in range(row,2)if ex[i][j]),None)
   assert choice==echoice
   if choice is None:continue
   ex[row],ex[choice]=ex[choice],ex[row];ed=ex[row][j];ex[row]=[v/ed for v in ex[row]]
   for ii in range(2):
    if ii!=row:
     ea=ex[ii][j];ex[ii]=[v-ea*w for v,w in zip(ex[ii],ex[row])]
   rows[row],rows[choice]=rows[choice],rows[row];fr[row],fr[choice]=fr[choice],fr[row]
   den=rows[row][j];assert den.lo*den.hi>0;pivots.append(den.bounds());df=fr[row][j];rows[row]=[x/den for x in rows[row]];fr[row]=[x/df for x in fr[row]]
   for i in range(2):
    if i!=row:
     a=rows[i][j];af=fr[i][j];rows[i]=[x-a*y for x,y in zip(rows[i],rows[row])];fr[i]=[x-af*y for x,y in zip(fr[i],fr[row])]
   pivs.append(j);row+=1
   if row==2:break
  expected=2 if k%2==0 and k<10 else 1
  assert len(pivs)==expected
  # Odd c is identically zero; k10 scalar has no nullspace.
  if k%2:assert all(x==0 for x in cf)
  N=[]
  for j in range(11-k):
   if j in pivs:continue
   v=[I(0)for _ in range(11-k)];v[j]=I(1)
   for i,pv in enumerate(pivs):v[pv]=-rows[i][j]
   N.append(v)
  NN.append(N);indices.extend((k,i,j)for i in range(len(N))for j in range(i,len(N)))
 assert len(indices)==190
 archived=json.loads(Path(certificate or 'proof_work/d10_exact_contact_psd_seed1_v1.json').read_text())
 seeddata=json.loads(Path(seed_input).read_text())if seed_input else None
 seedmodel=None if archived else json.loads(Path('proof_work/sharp_contact_refinement2026_results.json').read_text())['best_solution']
 Ts=[]
 for k,N in enumerate(NN):
  if not N:Ts.append([]);continue
  if archived:tq=[[F(x)for x in row]for row in archived['rational_basis_transforms'][k]]
  else:
   a=np.array([[float(F(v.lo+v.hi,2*S))for v in col]for col in N]).T;target=np.array(seedmodel['N'][k]);tt=np.linalg.lstsq(a,target,rcond=None)[0]
   tq=[[F(str(float(x))).limit_denominator(10**16)for x in row]for row in tt]
  Ts.append(tq)
  NN[k]=[[sum((N[j][i]*tq[j][q]for j in range(len(N))),I(0))for i in range(len(N[0]))]for q in range(len(N))]
 seed=[F(x)for x in (seeddata['seed']if seeddata else archived['seed'])];assert len(seed)==190
 chosen=[indices[j]for j in COLS]
 def jet(point):
  out=[[I(0)for _ in COLS]for _ in range(4)]
  for perm in itertools.permutations(range(3)):
   u,v,t=[point[i]for i in perm];a=t-u*v;b=(1-u*u)*(1-v*v);da=[-v,-u,I(1)];db=[-2*u*(1-v*v),-2*v*(1-u*u),I(0)]
   Q=[I(1),a];DQ=[[I(0)]*3,da]
   for k in range(1,10):
    Q.append(2*a*Q[-1]-b*Q[-2]);DQ.append([2*da[j]*Q[-2]+2*a*DQ[-1][j]-db[j]*Q[-3]-b*DQ[-2][j]for j in range(3)])
   powers=[]
   for k,N in enumerate(NN):
    if not N:powers.append(None);continue
    m=len(N[0]);up=[u**i for i in range(m)];vp=[v**i for i in range(m)];du=[I(0)]+[i*u**(i-1)for i in range(1,m)];dv=[I(0)]+[i*v**(i-1)for i in range(1,m)]
    powers.append([[sum((p[j]*n[j]for j in range(m)),I(0))for n in N]for p in [up,vp,du,dv]])
   for col,(k,i,j)in enumerate(chosen):
    pu,pv,dpu,dpv=powers[k];b0=pu[i]*pv[j];bu=dpu[i]*pv[j];bv=pu[i]*dpv[j]
    if i!=j:b0+=pu[j]*pv[i];bu+=dpu[j]*pv[i];bv+=pu[j]*dpv[i]
    out[0][col]+=Q[k]*b0/6
    for ax in range(3):out[perm[ax]+1][col]+=(DQ[k][ax]*b0+Q[k]*[bu,bv,I(0)][ax])/6
  return out
 nodes=[1-F(3,2)*rr*rr,2*rr*rr-1,rr*rr/2-1,I('-0.5'),rr/2,-rr];names='ABCDFG'
 geom=json.loads(Path('proof_work/candidate_triple_types_v1.json').read_text())['triangle_types'];diag=[jet([I(1),x,x])for x in nodes];f111=jet([I(1)]*3)[0];M=[];meta=[]
 for row in geom:
  lab=[names.index(a)for a in row['labels']];pt=[nodes[a]for a in lab];J=jet(pt)
  M.append([7*J[0][j]+sum((diag[a][0][j]for a in lab),I(0))+f111[j]/8 for j in range(190)]);meta.append(['value',row['labels']])
  grad=[[7*J[i+1][j]+diag[lab[i]][2][j]+diag[lab[i]][3][j]for j in range(190)]for i in range(3)]
  if row['status']!='identically_boundary':
   M.extend(grad);meta.extend([['gradient',row['labels'],i]for i in range(3)])
  else:
   u,v,t=pt;g=[2*(v*t-u),2*(u*t-v),2*(u*v-t)]
   for i in [1,2]:M.append([g[0]*grad[i][j]-g[i]*grad[0][j]for j in range(190)]);meta.append(['tangent',row['labels'],i])
 print('all190 analytic interval columns built seconds',time.time()-start,flush=True)
 if archived:cols=archived['selected_columns'];sel=archived['selected_rows']
 else:
  from scipy.linalg import qr
  mid=np.array([[float(F(x.lo+x.hi,2*S))for x in row]for row in M]);_,_,co=qr(mid,pivoting=True);cols=list(map(int,co[:33]));_,_,ro=qr(mid[:,cols].T,pivoting=True);sel=list(map(int,ro[:33]))
 assert len(set(cols))==len(set(sel))==33
 fv=[1/(2-2*x).sqrt()for x in nodes];fp=[fv[i]/(2-2*nodes[i])for i in range(6)];E=sum((w*x for w,x in zip([6,3,6,3,12,6],fv)),I(0));rhs=[]
 for kind,lab,*axis in meta:
  ix=[names.index(a)for a in lab]
  if kind=='value':rhs.append(sum((fv[a]for a in ix),I(0))-E/12)
  elif kind=='gradient':rhs.append(fp[ix[axis[0]]])
  else:
   u,v,t=[nodes[a]for a in ix];g=[2*(v*t-u),2*(u*t-v),2*(u*v-t)];i=axis[0];rhs.append(g[0]*fp[ix[i]]-g[i]*fp[ix[0]])
 res=[rhs[i]-sum((v*s for v,s in zip(M[i],seed)),I(0))for i in range(45)]
 A=[[M[i][j]for j in cols]+[res[i]]for i in sel];piv=[]
 for k in range(33):
  q=max(range(k,33),key=lambda i:abs(A[i][k].lo+A[i][k].hi));A[k],A[q]=A[q],A[k];d=A[k][k];assert d.lo*d.hi>0,('LU',k,d.pretty());piv.append(d.bounds())
  for i in range(k+1,33):
   fac=A[i][k]/d
   for j in range(k+1,34):A[i][j]-=fac*A[k][j]
   A[i][k]=I(0)
 delta=[I(0)]*33
 for i in reversed(range(33)):delta[i]=(A[i][-1]-sum((A[i][j]*delta[j]for j in range(i+1,33)),I(0)))/A[i][i]
 xx=[I(v)for v in seed]
 for i,j in enumerate(cols):xx[j]+=delta[i]
 # Correction magnitude is recorded; actual PSD validity is decided below by interval LDL.
 contact_errors=[rhs[i]-sum((M[i][j]*xx[j]for j in range(190)),I(0))for i in range(45)]
 assert all(e.lo<=0<=e.hi for e in contact_errors),[(i,e.pretty())for i,e in enumerate(contact_errors)if not(e.lo<=0<=e.hi)]
 lookup={v:i for i,v in enumerate(indices)};ldls=[];success=True
 for k,N in enumerate(NN):
  n=len(N)
  if not n:continue
  B=[[xx[lookup[k,min(i,j),max(i,j)]]for j in range(n)]for i in range(n)];ll=[[I(int(i==j))for j in range(n)]for i in range(n)];dd=[]
  for i in range(n):
   d=B[i][i]-sum((ll[i][j]**2*dd[j]for j in range(i)),I(0))
   if d.lo<=0:success=False;ldls.append({'k':k,'failed_pivot':i,'bounds':d.bounds(),'display':d.pretty()});break
   dd.append(d)
   for j in range(i+1,n):ll[j][i]=(B[j][i]-sum((ll[j][a]*ll[i][a]*dd[a]for a in range(i)),I(0)))/d
  else:ldls.append({'k':k,'positive_pivots':[d.bounds()for d in dd],'smallest_lower_display':min(float(F(d.lo,S))for d in dd)})
 out={'status':'CERTIFIED_CONTACT_AND_POSITIVE_DEFINITE'if success else 'PSD_INTERVAL_CHECK_FAILED','scope':'exact45contacts at true r_star by prior rank33 and W compatibility theorem, and reduced B positive definite; no global R nonnegativity','root_interval':[L,U],'bits':BITS,'source':'new rational convex seed corrected in archived analytic rationalT1 basis','seed_metadata':seeddata if seeddata else archived.get('seed_metadata'),'indices':[list(v)for v in indices],'rational_basis_transforms':[[[str(x)for x in row]for row in t]for t in Ts],'seed':[str(x)for x in seed],'selected_columns':cols,'selected_rows':sel,'row_meta':meta,'definition':'other157 coordinates equal rational seed; selected33 solve chosen contact equations at true stationary r_star','all45_contact_error_enclosures':[e.bounds()for e in contact_errors],'contact_exactness_basis':'33 selected exact equations plus certified rank33/W compatibility at true stationary root; interval zero containment is consistency check, not alone a proof','LU_pivots':piv,'delta_enclosures':[d.bounds()for d in delta],'max_abs_delta_upper':str(max(max(abs(d.lo),abs(d.hi))for d in delta))+'/'+str(S),'delta_display_max':max(float(F(max(abs(d.lo),abs(d.hi)),S))for d in delta),'reduced_solution_enclosures':[x.bounds()for x in xx],'PSD_LDL':ldls,'seconds':time.time()-start}
 
 if archived and not seeddata:
  for key in ['LU_pivots','delta_enclosures','reduced_solution_enclosures','PSD_LDL']:assert out[key]==archived[key],key
 path=Path(output);assert not path.exists();path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k]for k in ['status','delta_display_max','seconds']}),flush=True)
 if return_context:
  assert success
  return {'N':NN,'x':xx,'indices':indices,'nodes':nodes,'r':rr}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--output',default='proof_work/narrowroot2026_certificate.json');p.add_argument('--certificate');p.add_argument('--seed-input');a=p.parse_args();run(a.output,a.certificate,seed_input=a.seed_input)
