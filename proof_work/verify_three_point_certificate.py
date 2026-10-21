"""Exact-only verifier of rational nine-point three-point SDP certificates.
No numerical proposal/export files are read. All input coefficients are Fraction.
Usage: PYTHONPATH=proof_work/python_deps python3 proof_work/verify_three_point_certificate.py proof_work/three_point_d4_exact_25_735.json
"""
from fractions import Fraction as F
from pathlib import Path
import argparse,itertools,json,time
from certify_three_point_d4 import const,add,scale,mul,mono,permute,diag,ldl,bernstein,split,certify

def verify(path,budget,seconds):
 start=time.time();data=json.loads(Path(path).read_text())
 # Exact rationals only: no numerical proposal or floating eigenprojection.
 A=[[[F(v)for v in row]for row in block]for block in data['A']]
 assert [len(a)for a in A]==[5,4,3,2,1]
 for a in A:
  assert all(len(row)==len(a)for row in a)
  assert all(a[i][j]==a[j][i]for i in range(len(a))for j in range(len(a)))
  ldl(a)
 c=F(data['c']);H={(i,0,0):F(v)for i,v in enumerate(data['h_monomial'])if F(v)}
 hb=bernstein(H,degrees=(11,0,0));assert min(hb.flat)>0
 q=add(const(1),scale(mul(add(const(2),scale(mono(0,1),-2)),mul(H,H)),-1))
 stack=[bernstein(q,degrees=(23,0,0))];count=0
 while stack:
  b=stack.pop();count+=1
  if min(b.flat)>=0:continue
  assert count<100000,'minorant verification budget exhausted'
  stack.extend(split(b,0))
 u,v,t=(mono(i,1)for i in range(3));a=add(t,scale(mul(u,v),-1))
 b=mul(add(const(1),scale(mul(u,u),-1)),add(const(1),scale(mul(v,v),-1)))
 Q=[const(1),a]
 for k in range(1,4):Q.append(add(scale(mul(a,Q[-1]),2),scale(mul(b,Q[-2]),-1)))
 kernel={}
 for k in range(5):
  for i in range(5-k):
   for j in range(5-k):kernel=add(kernel,scale(mul(mul(mono(0,i),mono(1,j)),Q[k]),A[k][i][j]))
 polyF=scale(add(*(permute(kernel,p)for p in itertools.permutations(range(3)))),F(1,6))
 assert all(permute(polyF,p)==polyF for p in itertools.permutations(range(3)))
 Hsum=add(*(permute(H,p)for p in [(0,1,2),(1,0,2),(2,1,0)]))
 residual=add(Hsum,scale(polyF,-7),*(scale(diag(polyF,i),-1)for i in range(3)),const(-c))
 stored={tuple(a):F(v)for a,v in data['residual_monomial']if F(v)}
 assert residual==stored,'Stored residual differs from exact reconstruction'
 assert all(permute(residual,p)==residual for p in itertools.permutations(range(3)))
 bound=12*c-F(3,2)*sum(polyF.values());assert bound==F(data['target'])
 gram=add(const(1),scale(mul(mul(u,v),t),2),*(scale(mul(w,w),-1)for w in (u,v,t)))
 print('Exact-only LDL, minorant, kernel reconstruction, symmetry and bound identity PASS:',bound,flush=True)
 result=certify(bernstein(residual),bernstein(gram,upper=True),budget,seconds)
 report={'certificate':str(Path(path).resolve()),'bound_exact':str(bound),'input_arithmetic':'Fraction of saved rational strings only; no numerical proposal files','minorant_bernstein_nodes':count,'global':result,'total_seconds':time.time()-start}
 dest=Path(path).with_name(Path(path).stem+'_verified.json');dest.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)
 return result['status']=='certified'
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('certificate');p.add_argument('--budget',type=int,default=300000);p.add_argument('--seconds',type=int,default=240);a=p.parse_args();raise SystemExit(0 if verify(a.certificate,a.budget,a.seconds)else 2)
