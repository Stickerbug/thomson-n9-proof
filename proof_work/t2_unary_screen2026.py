"""Root-only two-dimensional screening; low cells are retained, never certified away."""
if not __debug__: raise RuntimeError('Assertions required')
from pathlib import Path
from fractions import Fraction as F
from math import lcm
from collections import Counter
import json,time,hashlib,numpy as np
from exact_tensor_bernstein import coefficients
from certify_all_degree import I,S
from verify_fixed_triangle_two_caps_widened_v1 import add,mul,split
BASE=Path(__file__).parent
Q=1<<128;BITS=64;TAU=F(1,5000);EPS=F(1,10**25)
def run(depth_limit=14,seconds=90):
 start=time.monotonic();src=BASE/'nonsharp_d10_root25_7599205_v10.json';inputpath=BASE/'two_other_valleys2026_probe.json'
 model=json.loads(src.read_text());row=next(x for x in json.loads(inputpath.read_text())['results']if x['name']=='T2')
 U,V,T=map(F,row['triangle_decimal']);g=1+2*U*V*T-U*U-V*V-T*T;assert g>0
 b=(1-I(U)**2).sqrt();actual=[[I(1),I(0),I(0)],[I(U),b,I(0)],[I(V),(T-I(U)*V)/b,I(g).sqrt()/b]]
 anchors=[]
 for ar in actual:
  rr=[]
  for x in ar:
   a=(x.lo*Q)//S
   assert F(a,Q)<=F(x.lo,S)<=F(x.hi,S)<F(a+1,Q)
   rr.append(a)
  anchors.append(rr)
 terms=[(tuple(e),F(z))for e,z in model['residual_monomial']];assert all(sum(e)<=27 for e,z in terms)
 deriv=sum(abs(c)*(e[1]+e[2])for e,c in terms);assert (1+F(3,Q))**26<2
 err=F(18,Q)*deriv;assert err<EPS
 cs=[];den=1
 for edge in (U,V,T):
  c={}
  for (i,j,k),z in terms:c[j,k]=c.get((j,k),F(0))+z*edge**i
  cs.append(c)
  for z in c.values():den=lcm(den,z.denominator)
 cs=[{e:z.numerator*(den//z.denominator)for e,z in c.items()}for c in cs]
 d={(0,0):Q,(2,0):Q,(0,2):Q};dp=[np.ones((1,1),dtype=object)]
 for _ in range(27):dp.append(mul(dp[-1],d))
 box=[(F(-1),F(1))]*2;dpoly={(i,j):F(int(z),Q**27)for (i,j),z in np.ndenumerate(dp[27])if z}
 du=coefficients(dpoly,box,degrees=(54,54),bits=BITS,upper=True)
 results=[]
 for sign in (1,-1):
  ns=[{(0,0):sign*c,(1,0):2*a,(0,1):2*b,(2,0):-sign*c,(0,2):-sign*c}for a,b,c in anchors];p=np.zeros((1,1),dtype=object)
  for (ii,jj),c in zip([(0,1),(0,2),(1,2)],cs):
   outer=np.zeros((1,1),dtype=object)
   for j in range(27,-1,-1):
    n=27-j;h=np.zeros((1,1),dtype=object)
    for k in range(n,-1,-1):
     if k<n:h=mul(h,ns[jj])
     cc=c.get((j,k),0)
     if cc:h=add(h,dp[n-k]*cc)
    outer=add(mul(outer,ns[ii]),h)
   p=add(p,outer)
  poly={(i,j):F(int(z),den*Q**27)for (i,j),z in np.ndenumerate(p)if z};bp=coefficients(poly,box,degrees=(54,54),bits=BITS)
  threshold=TAU+EPS;br=bp-np.array([-((-int(z)*threshold.numerator)//threshold.denominator)for z in du.flat],dtype=object).reshape(du.shape)
  cuts=[]
  for ni in ns:
   cc={e:F(z,Q)for e,z in ni.items()};cap=F(14,25)+F(3,Q)
   for e in d:cc[e]=cc.get(e,F(0))-cap
   cuts.append(coefficients(cc,box,degrees=(2,2),bits=BITS))
  cuts.append(coefficients({(2,0):F(1),(0,2):F(1),(0,0):F(-1)},box,degrees=(2,2),bits=BITS))
  stack=[([br]+cuts,0,(0,0,0,0))];leaves=[];nodes=0;clock=time.monotonic()
  while stack and time.monotonic()-clock<seconds:
   arr,depth,loc=stack.pop();nodes+=1;mins=[int(z.min())for z in arr]
   if max(mins[1:])>0:kind='excluded_anchor_or_disk'
   elif mins[0]>=0:kind='phi_high'
   elif depth>=depth_limit:kind='low_pending'
   else:
    ax=depth%2;parts=[split(z,ax)for z in arr];x,dx,y,dy=loc
    ll=[(2*x,dx+1,y,dy),(2*x+1,dx+1,y,dy)]if ax==0 else[(x,dx,2*y,dy+1),(x,dx,2*y+1,dy+1)]
    stack.append(([a[1]for a in parts],depth+1,ll[1]));stack.append(([a[0]for a in parts],depth+1,ll[0]));continue
   leaves.append({'location':loc,'kind':kind,'lower_coefficients':mins})
  for arr,depth,loc in stack:leaves.append({'location':loc,'kind':'budget_pending'})
  counts=Counter(l['kind']for l in leaves);area=Counter()
  for l in leaves:
   x,dx,y,dy=l['location'];area[l['kind']]+=F(4,1<<(dx+dy))
  assert sum(area.values(),F(0))==4
  out={'sign':sign,'nodes':nodes,'counts':dict(counts),'area':{k:str(v)for k,v in area.items()},'leaves':leaves,'seconds':time.monotonic()-clock}
  results.append(out);print('CHART',sign,'nodes',nodes,'counts',dict(counts),'areas',out['area'],flush=True)
 result={'status':'partial_unary_screen_not_pair_certificate','threshold':str(TAU),'root_coverage':'two hemisphere disks embedded in square charts; retained terminal rectangles cover all unresolved points','rounding_error_upper':str(err),'triangle':list(map(str,(U,V,T))),'anchors_dyadic':anchors,'anchor_denominator':str(Q),'bits':BITS,'max_depth':depth_limit,'results':results,'seconds':time.monotonic()-start,'dependencies':{str(p.name):hashlib.sha256(p.read_bytes()).hexdigest()for p in [src,inputpath,BASE/'exact_tensor_bernstein.py',BASE/'verify_fixed_triangle_two_caps_widened_v1.py',Path(__file__)]},'claim':'Every retained feasible point is either phi>=1/5000 or in a pending rectangle. No lower bound asserted on pending cells. If either member of a pair is phi_high, W>=1/25000 follows conditional on archived R>=0 and pair caps.'}
 output=BASE/'t2_unary_screen2026_result.json';output.write_text(json.dumps(result,indent=2)+'\n');print('SAVED',output,flush=True)
 return result
if __name__=='__main__':run()
