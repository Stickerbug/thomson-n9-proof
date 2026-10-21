if not __debug__:
 raise RuntimeError('Run certificate without -O or PYTHONOPTIMIZE')
"""Exact rational reconstruction and outward Bernstein proof for antipodal subproblem."""
from certify_three_point_d4 import F,add,const,scale,mul,mono,power,ldl,bernstein,split
from certify_d4_int64 import split64,safe_array
from pathlib import Path
from math import comb
import numpy as np,json,time

def run():
 start=time.time();base=Path(__file__).parent;src=json.loads((base/'antipodal_anchor2580_2026_export.json').read_text())
 z,w,t=(mono(i,1)for i in range(3));a=add(t,scale(mul(z,w),-1));b=mul(add(const(1),scale(mul(z,z),-1)),add(const(1),scale(mul(w,w),-1)))
 Q=[const(1),a]
 for k in range(1,3):Q.append(add(scale(mul(a,Q[-1]),2),scale(mul(b,Q[-2]),-1)))
 kernel={};piv=[]
 for block in src['blocks']:
  k=block['k'];ps=block['powers'];A=[list(map(F,row))for row in block['A']]
  assert len(A)==len(ps) and all(len(row)==len(ps)for row in A)
  assert all(A[i][j]==A[j][i]for i in range(len(ps))for j in range(len(ps)))
  piv.append(ldl(A))
  for i,pi in enumerate(ps):
   for j,pj in enumerate(ps):kernel=add(kernel,scale(mul(mul(mono(0,pi),mono(1,pj)),Q[k]),A[i][j]))
 saved=lambda key:{tuple(a):F(v)for a,v in src[key]if F(v)}
 assert kernel==saved('kernel_monomial')
 D={}
 for (i,j,k),v in kernel.items():D[(i+j,0,0)]=D.get((i+j,0,0),F(0))+v
 D={k:v for k,v in D.items()if v};assert D==saved('diag_z_monomial')
 h=list(map(F,src['h']));H={};fields={}
 for j,v in enumerate(h):
  if v:H[(0,0,j)]=v
  if j%2==0:
   fields=add(fields,{(j,0,0):v/3},{(0,j,0):v/3})
 DzDw=add(D,{(0,i,0):v for (i,_,_),v in D.items()})
 c=F(src['c']);target=F(src['target']);assert target==F(1,2)+21*c
 R=add(H,fields,scale(kernel,-1),scale(DzDw,-F(1,12)),const(-c));assert R==saved('residual_monomial')
 assert R=={(j,i,k):v for (i,j,k),v in R.items()}
 # Recheck h<=f on [-1,1] with exact arbitrary-precision Bernstein.
 h0={(i,0,0):v for i,v in enumerate(h)if v};hb=bernstein(h0,degrees=(11,0,0));assert min(hb.flat)>0
 test=add(const(1),scale(mul(add(const(2),scale(z,-2)),mul(h0,h0)),-1));stack=[bernstein(test,degrees=(23,0,0))];unodes=0
 while stack:
  bb=stack.pop();unodes+=1
  if min(bb.flat)>=0:continue
  assert unodes<100000;stack.extend(split(bb,0))
 # Transform domain z,w in [-.57,.57], t in [-1,.57] to cube [-1,1]^3.
 def transform(p):
  out={}
  for (i,j,k),v in p.items():
   for l in range(k+1):
    e=(i,j,l);value=v*F(57,100)**(i+j)*comb(k,l)*F(-43,200)**(k-l)*F(157,200)**l
    out[e]=out.get(e,F(0))+value
  return {a:v for a,v in out.items()if v}
 gram=add(const(1),scale(mul(mul(z,w),t),2),*(scale(mul(x,x),-1)for x in [z,w,t]))
 bits=48;B=safe_array(bernstein(transform(R),bits=bits));G=safe_array(bernstein(transform(gram),bits=bits,upper=True))
 bounds=[int(B.min()),int(B.max()),int(G.min()),int(G.max())]
 print('PASS exact PSD, reconstruction, h minorant; tensor',B.shape,'bounds',bounds,flush=True)
 stack=[(B,G,0,(0,0,0),((-1,1),)*3)];nodes=positive=outside=md=0
 while stack and nodes<1000000 and time.time()-start<120:
  bb,gg,depth,ds,box=stack.pop();nodes+=1;md=max(md,depth)
  if bb.min()>=0:positive+=1;continue
  # z,w exchange only, never all-three permutation.
  if gg.max()<0 or (box[0][0]<<ds[1])>(box[1][1]<<ds[0]):outside+=1;continue
  assert max(ds)<=80, 'Depth guard reached; no certificate'
  axis=min(range(3),key=lambda i:ds[i]);dd=list(ds);dd[axis]+=1;dd=tuple(dd)
  bl,br=split64(bb,axis);gl,gr=split64(gg,axis,True)
  lo,hi=box[axis];mid=lo+hi;lb=list(box);rb=list(box);lb[axis]=(2*lo,mid);rb[axis]=(mid,2*hi)
  stack.extend([(br,gr,depth+1,dd,tuple(rb)),(bl,gl,depth+1,dd,tuple(lb))])
  if nodes%50000==0:print('progress',nodes,'pending',len(stack),'seconds',time.time()-start,flush=True)
 result={'status':'certified'if not stack else 'unresolved','target':str(target),'source':'antipodal_anchor2580_2026_export.json','nodes':nodes,'positive_leaves':positive,'excluded_leaves':outside,'pending':len(stack),'maxdepth':md,'bits':bits,'initial_coefficient_bounds':bounds,'minorant_nodes':unodes,'psd_pivots':piv,'seconds':time.time()-start,'claim':'Any configuration containing an antipodal pair with remaining z,w in [-.57,.57] and all remaining pair dot products <=.57 has Coulomb energy >=25.80. Competitiveness forces stronger |z|<=.56 and t<.56, so all competitive antipodal configurations are excluded.'}
 dest=base/'antipodal_anchor2580_2026_verified.json';assert not dest.exists();dest.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
if __name__=='__main__':run()
