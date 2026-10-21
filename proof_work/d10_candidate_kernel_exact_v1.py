"""Independent polynomial-ring reconstruction of all d10 candidate kernel sums."""
import sympy as s,json,time
from sympy.polys.rings import ring
from sympy.polys.domains import QQ
from fractions import Fraction as F
from pathlib import Path
from candidate_low_rank import features
R,r=ring('r',QQ);x=s.symbols('r');zero=R.zero;one=R.one

def conv(a):return R.from_expr(s.sympify(a))
def run():
 start=time.time();nodes=[one-QQ(3,2)*r*r,2*r*r-one,r*r/2-one,-one/2,r/2,-r]
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
    for k in range(1,10):Q.append(2*a*Q[-1]-b*Q[-2])
    data.append((w,[u**i for i in range(11)],[v**i for i in range(11)],Q))
 rows=[]
 for k in range(11):
  pp,cc=features(x,k,11-k);p=[conv(t)for t in pp];c=[conv(t)for t in cc];m=11-k
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
  rows.append({'k':k,'matrix_size':m,'nullity':len(N),'exact_G_feature_identity':True,'exact_N_annihilation':True,'rank_pivot_polynomial':str(det.as_expr())});print('k',k,'verified seconds',time.time()-start,flush=True)
 out={'status':'CERTIFIED_EXACT_d10_CANDIDATE_KERNEL_IDENTITIES','blocks':rows,'arithmetic':'QQ[r] polynomial identities, independent ordered anchor sum with weights6,3','seconds':time.time()-start,'scope':'exact G identity and polynomial nullspace annihilation; rank interval checks are separate'}
 p=Path('proof_work/d10_candidate_kernel_exact_v1.json');assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');print('PASS all k0..10',time.time()-start,flush=True)
if __name__=='__main__':run()
