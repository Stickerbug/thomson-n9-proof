"""70-bit Python-object outward Bernstein replay with exact symmetry pruning and fast exact sums.
Rebuild exact rational kernel and minorant; shares reviewed exact transform with parent.
"""
if not __debug__:
 raise RuntimeError('Exact certificate replay requires active assertions; do not use python -O/PYTHONOPTIMIZE.')
from pathlib import Path
from fractions import Fraction as F
import argparse,itertools,json,time
from certify_three_point_d4 import add,const,scale,mul,mono,permute,diag,ldl,split
from certify_conditional_h19 import check
from exact_tensor_bernstein import coefficients
ROOT=Path(__file__).parent

def split_fast(B,axis,upper=False):
 import numpy as np
 a=np.moveaxis(B,axis,0);n=len(a)-1;row=a.copy();left=np.empty_like(a);right=np.empty_like(a);left[0]=row[0];right[0]=row[-1]
 for j in range(1,n+1):
  row=row[:-1]+row[1:];den=1<<j
  left[j]=-((-row[0])//den)if upper else row[0]//den
  right[j]=-((-row[-1])//den)if upper else row[-1]//den
 return np.moveaxis(left,0,axis),np.moveaxis(right[::-1],0,axis)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--model',default='proof_work/d10_best_rational_target25_758_v1.json');ap.add_argument('--out',required=True);ap.add_argument('--seconds',type=float,default=120);ap.add_argument('--budget',type=int,default=200000);args=ap.parse_args();out=Path(args.out);assert not out.exists();start=time.time();src=json.loads(Path(args.model).read_text());degree=int(src['degree']);A=[[[F(v)for v in row]for row in a]for a in src['A']]
 assert [len(a)for a in A]==list(range(degree+1,0,-1));pivots=[]
 for a in A:
  assert all(len(row)==len(a)for row in a);assert all(a[i][j]==a[j][i]for i in range(len(a))for j in range(len(a)));pivots.append(ldl(a))
 h=[F(v)for v in src['h_monomial']];lo,hi=F(-1),F(14,25);pos=check(h,lo,hi)
 def conv(a,b):
  ans=[F(0)]*(len(a)+len(b)-1)
  for i,x in enumerate(a):
   for j,y in enumerate(b):ans[i+j]+=x*y
  return ans
 hh=conv([F(2),F(-2)],conv(h,h));qh=[-x for x in hh];qh[0]+=1;minor=check(qh,lo,hi)
 u,v,t=[mono(i,1)for i in range(3)];aa=add(t,scale(mul(u,v),-1));bb=mul(add(const(1),scale(mul(u,u),-1)),add(const(1),scale(mul(v,v),-1)));Q=[const(1),aa]
 for k in range(1,degree):Q.append(add(scale(mul(aa,Q[-1]),2),scale(mul(bb,Q[-2]),-1)))
 raw={}
 for k,a in enumerate(A):
  for i,row in enumerate(a):
   for j,cij in enumerate(row):raw=add(raw,scale(mul(mul(mono(0,i),mono(1,j)),Q[k]),cij))
 poly=scale(add(*(permute(raw,p)for p in itertools.permutations(range(3)))),F(1,6));assert poly=={tuple(a):F(v)for a,v in src['F_monomial']if F(v)}
 c,target=F(src['c']),F(src['target']);assert 12*c-F(3,2)*sum(poly.values())==target
 hp={(i,0,0):c for i,c in enumerate(h)if c};r=add(*(permute(hp,p)for p in [(0,1,2),(1,0,2),(2,1,0)]),scale(poly,-7),*(scale(diag(poly,i),-1)for i in range(3)),const(-c));assert r=={tuple(a):F(v)for a,v in src['residual_monomial']if F(v)}
 gram=add(const(1),scale(mul(mul(u,v),t),2),*(scale(mul(x,x),-1)for x in [u,v,t]));bits=70
 B=coefficients(r,[(lo,hi)]*3,bits=bits);G=coefficients(gram,[(lo,hi)]*3,bits=bits,upper=True);assert B.dtype==object and G.dtype==object
 pair=json.loads((ROOT/'pair056_optimized_certificate.json').read_text());assert pair['status']=='certified';U=F(pair['U']);assert target<U
 initial_bounds=[str(min(B.flat)),str(max(B.flat)),str(min(G.flat)),str(max(G.flat))];print('OBJECT70_INITIAL',B.shape,initial_bounds,'seconds',time.time()-start,flush=True)
 assert all(permute(r,p)==r for p in itertools.permutations(range(3)));stack=[(B,G,0,(0,0,0),((-1,1),)*3)];nodes=positive=outside=symmetry=maxdepth=0;walk=time.time()
 while stack and nodes<args.budget and time.time()-walk<args.seconds:
  b,g,depth,ds,box=stack.pop();nodes+=1;maxdepth=max(maxdepth,depth)
  if (box[0][0]<<ds[1])>(box[1][1]<<ds[0]) or (box[1][0]<<ds[2])>(box[2][1]<<ds[1]):symmetry+=1;continue
  if min(b.flat)>=0:positive+=1;continue
  if max(g.flat)<0:outside+=1;continue
  assert max(ds)<100,'deep unresolved box; no certificate'
  axis=min(range(3),key=lambda i:ds[i]);dd=list(ds);dd[axis]+=1;dd=tuple(dd);bl,br=split_fast(b,axis);gl,gr=split_fast(g,axis,upper=True)
  l,h=box[axis];boxl=list(box);boxr=list(box);boxl[axis]=(2*l,l+h);boxr[axis]=(l+h,2*h)
  stack.extend([(br,gr,depth+1,dd,tuple(boxr)),(bl,gl,depth+1,dd,tuple(boxl))])
  if nodes%5000==0:print('OBJECT70_PROGRESS',nodes,'pending',len(stack),'depth',maxdepth,'seconds',time.time()-walk,flush=True)
 result={'status':'certified'if not stack else 'budget_exhausted','target':str(target),'source':str(Path(args.model).resolve()),'domain':[str(lo),str(hi)],'method':'70-bit outward Python-int object tensor Bernstein; exact Fraction reconstruction; Gram-negative plus exact symmetry pruning; NO int64 conversion; exact integer de Casteljau sums with final boundary rounding','bits':bits,'nodes':nodes,'positive_leaves':positive,'gram_negative_leaves':outside,'symmetry_leaves':symmetry,'pending':len(stack),'maxdepth':maxdepth,'initial_integer_bounds':initial_bounds,'h_positive_nodes':pos,'h_minorant_nodes':minor,'all_psd_ldl_positive':True,'psd_pivots':pivots,'normalization_exact':True,'pair_exclusion_dependency':str((ROOT/'pair056_optimized_certificate.json').resolve()),'pair_threshold_U':str(U),'unconditional_logic':'If E<=U, independently certified pair056 restricts all pair dot products to [-1,14/25]. Positive residual and PSD three-point identity give E>=target. If E>U then E>target. Pair056 itself is an explicit external exact certificate dependency.','seconds':time.time()-start}
 out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='psd_pivots'}),flush=True)
 raise SystemExit(0 if not stack else 2)
if __name__=='__main__':main()
