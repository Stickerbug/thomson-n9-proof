"""Independent polynomial-ring reconstruction of all d12 candidate kernel sums."""
if not __debug__:raise RuntimeError('Assertions are required for certificate verification')
import sympy as s,json,time,argparse
from sympy.polys.rings import ring
from sympy.polys.domains import QQ
from fractions import Fraction as F
from pathlib import Path
from candidate_low_rank import features
from dyadic_interval import I
from certify_pair_moments import L,U
R,r=ring('r',QQ);x=s.symbols('r');zero=R.zero;one=R.one
def enclosure(poly):
 ans=I(0);rr=I(L,U)
 for q in s.Poly(poly.as_expr(),x).all_coeffs():ans=ans*rr+I(str(q))
 return ans

def conv(a):return R.from_expr(s.sympify(a))
def run(output):
 start=time.time();rr=I(L,U);assert rr.lo>0 and rr.hi<I(1).lo;assert (1-rr*rr).lo>0
 nodes=[one-QQ(3,2)*r*r,2*r*r-one,r*r/2-one,-one/2,r/2,-r]
 def dot(i,j):
  if i==j:return one
  if i>=6 and j>=6:return nodes[3]
  if i>=6:i,j=j,i
  if j>=6:return nodes[5]if (j-6-i%3)%3==1 else nodes[4]
  return nodes[0]if i//3==j//3 else nodes[1]if i%3==j%3 else nodes[2]
 data=[]
 for anchor,w in [(0,6),(6,3)]:
  for y in range(9):
   for z in range(9):
    u,v,t=dot(anchor,y),dot(anchor,z),dot(y,z);a=t-u*v;b=(one-u*u)*(one-v*v);Q=[one,a]
    for k in range(1,12):Q.append(2*a*Q[-1]-b*Q[-2])
    data.append((w,[u**i for i in range(13)],[v**i for i in range(13)],Q))
 rows=[]
 for k in range(13):
  pp,cc=features(x,k,13-k);p=[conv(t)for t in pp];c=[conv(t)for t in cc];m=13-k
  for i in range(m):
   for j in range(i,m):
    g=sum((w*u[i]*v[j]*q[k]for w,u,v,q in data),zero)
    assert g==6*(one-r*r)**(k%2)*p[i]*p[j]+3*c[i]*c[j],(k,i,j)
  # Polynomial cross-product nullbasis, with no unknown zero decisions.
  if k%2:assert all(t==zero for t in c)
  if k%2==0 and m>=2:
   a,b=next((i,j)for i in range(m)for j in range(i+1,m)if p[i]*c[j]-p[j]*c[i]);det=p[a]*c[b]-p[b]*c[a];N=[]
   for j in range(m):
    if j in (a,b):continue
    v=[zero]*m;v[j]=det;v[a]=p[b]*c[j]-p[j]*c[b];v[b]=p[j]*c[a]-p[a]*c[j];N.append(v)
  else:
   a=next(i for i in range(m)if p[i]);det=p[a];N=[]
   for j in range(m):
    if j==a:continue
    v=[zero]*m;v[j]=det;v[a]=-p[j];N.append(v)
  for v in N:assert sum((a*b for a,b in zip(v,p)),zero)==zero and sum((a*b for a,b in zip(v,c)),zero)==zero
  piv=enclosure(det);assert piv.lo*piv.hi>0
  assert len(N)==([11,11,9,9,7,7,5,5,3,3,1,1,0][k])
  rows.append({'rank':m-len(N),'rank_pivot_bounds':piv.bounds(),'k':k,'matrix_size':m,'nullity':len(N),'exact_G_feature_identity':True,'exact_N_annihilation':True,'rank_pivot_polynomial':str(det.as_expr())});print('k',k,'verified seconds',time.time()-start,flush=True)
 assert sum(v['nullity']*(v['nullity']+1)//2 for v in rows)==322
 out={'reduced_symmetric_variables':322,'root_interval':[L,U],'status':'CERTIFIED_EXACT_d12_CANDIDATE_KERNEL_IDENTITIES','blocks':rows,'arithmetic':'QQ[r] polynomial identities, independent ordered anchor sum with weights6,3','seconds':time.time()-start,'scope':'exact G feature identity and complete polynomial nullspaces; all rank pivots interval-certified over true-root bracket; not PSD feasibility or global residual proof'}
 p=Path(output);assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');print('PASS all k0..12',time.time()-start,flush=True)
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--output',default='proof_work/d12_candidate_kernel_exact2026.json');a=p.parse_args();run(a.output)
