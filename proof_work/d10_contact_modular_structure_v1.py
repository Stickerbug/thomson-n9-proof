"""Finite-field specialization diagnostic ONLY, not an identity at r_star."""
import json,itertools,time
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from candidate_low_rank import features,nullspace_two_rows

def run(prime,r):
 p=prime
 def cv(x):x=F(x);return x.numerator*pow(x.denominator,-1,p)%p
 rr=cv(r);iv=lambda x:pow(int(x)%p,-1,p)
 NN=[];inds=[]
 for k in range(11):
  a,c=features(r,k,11-k);ns=nullspace_two_rows(a,c);N=np.array([[cv(v)for v in col]for col in ns],dtype=np.int64).T if ns else np.empty((11-k,0),dtype=np.int64);NN.append(N)
  inds.extend((k,i,j)for i in range(len(ns))for j in range(i,len(ns)))
 assert len(inds)==190
 def jet(point):
  out=np.zeros((4,190),dtype=np.int64)
  for perm in itertools.permutations(range(3)):
   u,v,t=[int(point[a])for a in perm];a=(t-u*v)%p;b=((1-u*u)*(1-v*v))%p
   da=np.array([-v,-u,1],dtype=np.int64)%p;db=np.array([-2*u*(1-v*v),-2*v*(1-u*u),0],dtype=np.int64)%p
   Q=[1,a];DQ=[np.zeros(3,dtype=np.int64),da]
   for k in range(1,10):
    Q.append((2*a*Q[-1]-b*Q[-2])%p);DQ.append((2*da*Q[-2]+2*a*DQ[-1]-db*Q[-3]-b*DQ[-2])%p)
   j0=0
   for k,N in enumerate(NN):
    m=len(N);up=np.array([pow(u,i,p)for i in range(m)],dtype=np.int64);vp=np.array([pow(v,i,p)for i in range(m)],dtype=np.int64)
    du=np.array([0]+[i*pow(u,i-1,p)%p for i in range(1,m)],dtype=np.int64);dv=np.array([0]+[i*pow(v,i-1,p)%p for i in range(1,m)],dtype=np.int64)
    pu=up@N%p;pv=vp@N%p;dpu=du@N%p;dpv=dv@N%p
    for i in range(N.shape[1]):
     for j in range(i,N.shape[1]):
      b0=(pu[i]*pv[j]+(pu[j]*pv[i]if i!=j else 0))%p
      bu=(dpu[i]*pv[j]+(dpu[j]*pv[i]if i!=j else 0))%p;bv=(pu[i]*dpv[j]+(pu[j]*dpv[i]if i!=j else 0))%p
      out[0,j0]=(out[0,j0]+Q[k]*b0)%p
      gd=(DQ[k]*b0+Q[k]*np.array([bu,bv,0],dtype=np.int64))%p
      for a0,axis in enumerate(perm):out[axis+1,j0]=(out[axis+1,j0]+gd[a0])%p
      j0+=1
  return out*iv(6)%p
 nodes=[1-F(3,2)*r*r,2*r*r-1,r*r/2-1,F(-1,2),r/2,-r];ni=[cv(x)for x in nodes];labels='ABCDFG';weight=[6,3,6,3,12,6]
 geom=json.loads(Path('proof_work/candidate_triple_types_v1.json').read_text())['triangle_types']
 diag=[jet([1,x,x])for x in ni];f111=jet([1,1,1])[0];M=[];H=[];meta=[]
 def rhs(lab):
  q=np.array([-w*iv(12)%p for w in weight],dtype=np.int64)
  for a in lab:q[a]=(q[a]+1)%p
  return q
 for row in geom:
  lab=[labels.index(a)for a in row['labels']];point=[ni[a]for a in lab];J=jet(point)
  val=(7*J[0]+sum((diag[a][0]for a in lab),np.zeros(190,dtype=np.int64))+f111*iv(8))%p
  grad=np.array([(7*J[i+1]+diag[lab[i]][2]+diag[lab[i]][3])%p for i in range(3)])
  M.append(val);H.append(rhs(lab));meta.append(['value',row['labels']])
  HG=np.zeros((3,6),dtype=np.int64)
  for i,a in enumerate(lab):HG[i,a]=iv(2-2*ni[a])
  if row['status']!='identically_boundary':
   for i in range(3):M.append(grad[i]);H.append(HG[i]);meta.append(['gradient',row['labels'],i])
  else:
   u,v,t=point;g=np.array([2*(v*t-u),2*(u*t-v),2*(u*v-t)],dtype=np.int64)%p;assert g[0]
   for i in [1,2]:
    M.append((g[0]*grad[i]-g[i]*grad[0])%p);H.append((g[0]*HG[i]-g[i]*HG[0])%p);meta.append(['tangent',row['labels'],i])
 M=np.array(M,dtype=np.int64);H=np.array(H,dtype=np.int64);assert M.shape==(45,190)
 H[:,0]=(H[:,0]+rr*H[:,3])%p;H=H[:,[0,1,2,4,5]]
 A=np.column_stack([M,H]);row=0;piv=[]
 for col in range(190):
  choice=next((j for j in range(row,45)if A[j,col]),None)
  if choice is None:continue
  A[[row,choice]]=A[[choice,row]];A[row]=A[row]*iv(A[row,col])%p
  for j in range(45):
   if j!=row and A[j,col]:A[j]=(A[j]-A[j,col]*A[row])%p
  piv.append(col);row+=1
 leftovers=A[row:,190:];dnode=[-3*r,4*r,r,F(0),F(1,2),F(-1)]
 ep=np.array([cv(weight[i]*dnode[i]/(2-2*nodes[i]))for i in range(6)],dtype=np.int64);ep[0]=(ep[0]+rr*ep[3])%p;ep=ep[[0,1,2,4,5]]
 assert ep[0]
 multiples=[bool(np.all((v-v[0]*iv(ep[0])*ep)%p==0))for v in leftovers]
 assert row==33 and all(multiples) and any(np.any(v)for v in leftovers)
 return {'prime':p,'r':str(r),'contact_plus_tangent_rank':row,'unknowns':190,'residual_rhs_dimension_after_fD_equals_r_fA':1,'all_rhs_obstructions_proportional_to_Eprime':all(multiples),'pivot_columns':piv,'nonzero_leftover_rows':sum(bool(np.any(v))for v in leftovers),'scope':'exact finite-field specialization only; does not certify rank or identity at r_star'}
if __name__=='__main__':
 start=time.time();rows=[run(1009,F(7,10)),run(1013,F(5,7))];out={'status':'specializations_passed_NOT_global_proof','checks':rows,'seconds':time.time()-start};path=Path('proof_work/d10_contact_modular_structure_v1.json');assert not path.exists();path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
