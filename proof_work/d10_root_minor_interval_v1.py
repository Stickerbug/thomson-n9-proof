"""Root-interval 33minor lower rank certificate, conditional on feature formula."""
import itertools,json,time,argparse
import sympy as sp
from pathlib import Path
from fractions import Fraction as F
import numpy as np
from candidate_low_rank import features
from dyadic_interval import I,BITS,S
from certify_pair_moments import L,U
COLS=list(range(27))+[45,46,54,55,56,57]

def run(output):
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
  M.append([7*J[0][j]+sum((diag[a][0][j]for a in lab),I(0))+f111[j]/8 for j in range(33)]);meta.append(['value',row['labels']])
  grad=[[7*J[i+1][j]+diag[lab[i]][2][j]+diag[lab[i]][3][j]for j in range(33)]for i in range(3)]
  if row['status']!='identically_boundary':
   M.extend(grad);meta.extend([['gradient',row['labels'],i]for i in range(3)])
  else:
   u,v,t=pt;g=[2*(v*t-u),2*(u*t-v),2*(u*v-t)]
   for i in [1,2]:M.append([g[0]*grad[i][j]-g[i]*grad[0][j]for j in range(33)]);meta.append(['tangent',row['labels'],i])
 print('interval45x33 built seconds',time.time()-start,flush=True)
 from scipy.linalg import qr
 mid=np.array([[float(F(x.lo+x.hi,2*S))for x in row]for row in M]);_,_,order=qr(mid.T,pivoting=True);sel=list(map(int,order[:33]));A=[[x for x in M[i]]for i in sel];lu=[];swaps=[]
 for k in range(33):
  q=max(range(k,33),key=lambda j:abs(A[j][k].lo+A[j][k].hi));A[k],A[q]=A[q],A[k];swaps.append(q);d=A[k][k]
  if d.lo*d.hi<=0:
   out={'status':'FAILED_interval_pivot_contains_zero','pivot':k,'bounds':d.bounds(),'display':d.pretty(),'selected_rows':sel,'seconds':time.time()-start};break
  lu.append({'bounds':d.bounds(),'display':d.pretty()})
  for i in range(k+1,33):
   a=A[i][k]/d
   for j in range(k+1,33):A[i][j]-=a*A[k][j]
   A[i][k]=I(0)
 else:out={'status':'CERTIFIED_33minor_NONZERO','rank_lower_bound':33,'selected_columns':COLS,'selected_rows':sel,'selected_row_meta':[meta[i]for i in sel],'row_swaps':swaps,'LU_pivots':lu,'feature_pivots':pivots,'root_interval':[L,U],'bits':BITS,'seconds':time.time()-start,'zero_pattern_checked_over_Qr':True,'scope':'interval ranklower for selected analytic features; not full kernel identity, compatibility, PSD or global residual proof'}
 path=Path(output);assert not path.exists();path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k in ['status','pivot','display','seconds']}),flush=True)
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--output',default='proof_work/d10_root_minor_interval_v2.json');a=p.parse_args();run(a.output)
