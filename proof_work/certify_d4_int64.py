"""Exact integer Bernstein certificate with proven-safe int64 subdivision."""
from certify_three_point_d4 import F,add,scale,const,mul,mono,bernstein
from pathlib import Path
import json,time,argparse,itertools
import numpy as np

def split64(B,axis,upper=False):
 w=np.moveaxis(B,axis,0).copy();n=len(w)-1
 left=np.empty_like(w);right=np.empty_like(w);left[0]=w[0];right[n]=w[-1]
 for j in range(1,n+1):
  s=w[:-1]+w[1:];w=-((-s)//2)if upper else s//2
  left[j]=w[0];right[n-j]=w[-1]
 return np.moveaxis(left,0,axis),np.moveaxis(right,0,axis)

def safe_array(A):
 # All descendants remain between original integer extrema, including outward averages.
 # Initial |coefficient|<2^60 => every addition has |sum|<2^61, far below int64 limits.
 assert all(abs(int(v))<2**60 for v in A.flat)
 return A.astype(np.int64)

def main(target,budget,seconds):
 start=time.time();base=Path(__file__).parent
 src=json.loads((base/'three_point_d4_exact_25_745.json').read_text())
 R={tuple(a):F(v)for a,v in src['residual_monomial']}
 R=add(R,const(-(F(target)-F('25.745'))/12))
 assert all({tuple(a[p.index(i)]for i in range(3)):v for a,v in R.items()}==R for p in itertools.permutations(range(3)))
 u,v,t=(mono(i,1)for i in range(3));G=add(const(1),scale(mul(mul(u,v),t),2),*(scale(mul(x,x),-1)for x in [u,v,t]))
 bits=40;B=safe_array(bernstein(R,bits=bits));G=safe_array(bernstein(G,upper=True,bits=bits))
 coeff_bounds=[int(B.min()),int(B.max()),int(G.min()),int(G.max())]
 stack=[(B,G,0,(0,0,0),((-1.,1.),)*3)];nodes=pos=out=md=0
 # Box endpoints are dyadic with depth<50 so binary floats below are exact, used only symmetry pruning.
 while stack and nodes<budget and time.time()-start<seconds:
  b,g,depth,ds,box=stack.pop();nodes+=1;md=max(md,depth)
  assert max(ds)<50
  if b.min()>=0:pos+=1;continue
  if g.max()<0 or box[0][0]>box[1][1]or box[1][0]>box[2][1]:out+=1;continue
  axis=min(range(3),key=lambda i:ds[i]);dd=list(ds);dd[axis]+=1;dd=tuple(dd)
  bl,br=split64(b,axis);gl,gr=split64(g,axis,True)
  mid=(box[axis][0]+box[axis][1])/2;lb=list(box);rb=list(box);lb[axis]=(box[axis][0],mid);rb[axis]=(mid,box[axis][1])
  stack.extend([(br,gr,depth+1,dd,tuple(rb)),(bl,gl,depth+1,dd,tuple(lb))])
  if nodes%50000==0:print('progress',nodes,'pending',len(stack),'seconds',time.time()-start,flush=True)
 result={'target':target,'status':'certified'if not stack else 'budget_exhausted','nodes':nodes,'positive_leaves':pos,'excluded_leaves':out,'pending':len(stack),'maxdepth':md,'bits':bits,'coefficient_bounds':coeff_bounds,'source':'three_point_d4_exact_25_745.json','logic':'Source rational PSD/minorant certificate plus residual constant shifted by -(target-25.745)/12; full Gram domain. Exact integer outward Bernstein. All initial coefficients abs<2^60, convex/outward averaging preserves extrema so int64 additions abs<2^61. Binary box endpoints exact because each axis depth<50.','seconds':time.time()-start}
 dest=base/('d4_int64_'+target.replace('.','_')+'.json');assert not dest.exists();dest.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--target',default='25.7468');p.add_argument('--budget',type=int,default=2000000);p.add_argument('--seconds',type=float,default=600);a=p.parse_args();main(a.target,a.budget,a.seconds)
