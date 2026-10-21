"""Exact rational d4 model plus outward integer Bernstein subdivision.
No claim of proof unless status == certified. NumPy object arrays store integers only.
"""
from fractions import Fraction as F
from math import comb,factorial
from pathlib import Path
import itertools,json,time,argparse
import numpy as np
ZERO=(0,0,0)
def const(c):return {ZERO:F(c)} if c else {}
def add(*ps):
 o={}
 for p in ps:
  for a,c in p.items():o[a]=o.get(a,F(0))+c
 return {a:c for a,c in o.items() if c}
def scale(p,c):return {a:v*c for a,v in p.items() if v*c}
def mul(p,q):
 o={}
 for a,c in p.items():
  for b,d in q.items():
   k=tuple(x+y for x,y in zip(a,b));o[k]=o.get(k,F(0))+c*d
 return {a:c for a,c in o.items() if c}
def power(p,n):
 r=const(1)
 for _ in range(n):r=mul(r,p)
 return r
def mono(axis,n):
 a=[0]*3;a[axis]=n;return {tuple(a):F(1)}
def permute(p,perm):
 o={}
 for a,c in p.items():
  b=[0]*3
  for j in range(3):b[perm[j]]=a[j]
  o[tuple(b)]=c
 return o
def diag(p,axis):
 # F(1,t,t), mapped to coordinate axis.
 o={}
 for a,c in p.items():
  b=[0]*3;b[axis]=a[1]+a[2];b=tuple(b);o[b]=o.get(b,F(0))+c
 return o

def ldl(A):
 n=len(A);L=[[F(i==j)for j in range(n)]for i in range(n)];D=[]
 for i in range(n):
  pivot=A[i][i]-sum(L[i][k]**2*D[k]for k in range(i));assert pivot>0,(i,str(pivot));D.append(pivot)
  for j in range(i+1,n):L[j][i]=(A[j][i]-sum(L[j][k]*L[i][k]*D[k]for k in range(i)))/pivot
 return [str(v)for v in D]

def bernstein(p,degrees=None,upper=False,bits=70):
 deg=degrees or tuple(max((a[i]for a in p),default=0)for i in range(3))
 # Substitution x=2z-1 followed by power-to-Bernstein.
 q={}
 for a,c in p.items():
  for b in itertools.product(*(range(i+1)for i in a)):
   val=c
   for ai,bi in zip(a,b):val*=comb(ai,bi)*2**bi*(-1)**(ai-bi)
   q[b]=q.get(b,F(0))+val
 out=np.empty(tuple(i+1 for i in deg),dtype=object);S=1<<bits
 for index in np.ndindex(out.shape):
  val=F(0)
  for a,c in q.items():
   if all(ai<=ii for ai,ii in zip(a,index)):
    factor=F(1)
    for ai,ii,di in zip(a,index,deg):factor*=F(comb(ii,ai),comb(di,ai))
    val+=c*factor
  out[index]=-((-val.numerator*S)//val.denominator) if upper else val.numerator*S//val.denominator
 return out

def split(B,axis,upper=False):
 work=np.moveaxis(B,axis,0).copy();n=len(work)-1
 left=np.empty_like(work);right=np.empty_like(work);left[0]=work[0];right[n]=work[n]
 for j in range(1,n+1):
  s=work[:-1]+work[1:];work=-((-s)//2) if upper else s//2
  left[j]=work[0];right[n-j]=work[-1]
 return np.moveaxis(left,0,axis),np.moveaxis(right,0,axis)

def certify(B,G,budget,seconds):
 stack=[(B,G,0,(0,0,0),((F(-1),F(1)),)*3)];visited=positive=outside=0;worstdepth=0;start=time.time()
 while stack and visited<budget and time.time()-start<seconds:
  b,g,depth,depths,box=stack.pop();visited+=1;worstdepth=max(worstdepth,depth)
  if min(b.flat)>=0:positive+=1;continue
  if max(g.flat)<0 or box[0][0]>box[1][1] or box[1][0]>box[2][1]:outside+=1;continue
  axis=min(range(3),key=lambda i:depths[i]);ds=list(depths);ds[axis]+=1;ds=tuple(ds)
  bl,br=split(b,axis);gl,gr=split(g,axis,upper=True)
  mid=sum(box[axis])/2;leftbox=list(box);rightbox=list(box);leftbox[axis]=(box[axis][0],mid);rightbox[axis]=(mid,box[axis][1])
  stack.extend([(br,gr,depth+1,ds,tuple(rightbox)),(bl,gl,depth+1,ds,tuple(leftbox))])
  if visited%1000==0:print(json.dumps({'visited':visited,'pending':len(stack),'depth':depth,'seconds':time.time()-start}),flush=True)
 return {'status':'certified' if not stack else 'budget_exhausted','visited':visited,'positive_leaves':positive,'gram_or_symmetry_excluded_leaves':outside,'pending_boxes':len(stack),'max_depth':worstdepth,'seconds':time.time()-start,'minimum_pending_lower_coefficient':float(min(min(x[0].flat)for x in stack)/(1<<70)) if stack else None}

def run(target,budget,seconds):
 src=json.loads(Path(__file__).with_name('three_point_export.json').read_text());model=src['models']['4'];A=[];pivots=[]
 for raw in model['A_psd_projected_float']:
  n=len(raw);a=[[F(str(round((raw[i][j]+raw[j][i])/2,10)))+F(i==j,10**7)for j in range(n)]for i in range(n)]
  pivots.append(ldl(a));A.append(a)
 H={}
 for i,v in enumerate(src['h_monomial_ascending']):H[(i,0,0)]=F(str(round(v,12)))
 H=add(H,const(-F(1,10**7)))
 # f-h proof: h>=0, and 1-(2-2t)h^2>=0 imply h<=f.
 hbern=bernstein(H,degrees=(11,0,0));assert min(hbern.flat)>0
 q=add(const(1),scale(mul(add(const(2),scale(mono(0,1),-2)),mul(H,H)),-1))
 qb=bernstein(q,degrees=(23,0,0));todo=[qb];uni=0
 while todo:
  b=todo.pop();uni+=1
  if min(b.flat)>=0:continue
  assert uni<20000,'minorant certification budget exhausted'
  l,r=split(b,0);todo.extend([l,r])
 u,v,t=(mono(i,1)for i in range(3));a=add(t,scale(mul(u,v),-1));b=mul(add(const(1),scale(mul(u,u),-1)),add(const(1),scale(mul(v,v),-1)))
 Q=[const(1),a]
 for k in range(1,4):Q.append(add(scale(mul(a,Q[-1]),2),scale(mul(b,Q[-2]),-1)))
 kernel={}
 for k in range(5):
  for i in range(5-k):
   for j in range(5-k):kernel=add(kernel,scale(mul(mul(mono(0,i),mono(1,j)),Q[k]),A[k][i][j]))
 polyF=scale(add(*(permute(kernel,p)for p in itertools.permutations(range(3)))),F(1,6))
 assert all(permute(polyF,p)==polyF for p in itertools.permutations(range(3)))
 F111=sum(polyF.values());c=(F(target)+F(3,2)*F111)/12
 hs=add(*(permute(H,p)for p in [(0,1,2),(1,0,2),(2,1,0)]))
 residual=add(hs,scale(polyF,-7),*(scale(diag(polyF,i),-1)for i in range(3)),const(-c))
 gram=add(const(1),scale(mul(mul(u,v),t),2),*(scale(mul(w,w),-1)for w in [u,v,t]))
 print('Exact PSD and univariate minorant certified; building tensor Bernstein',flush=True)
 start=time.time();B=bernstein(residual);G=bernstein(gram,upper=True);print('Tensor shape',B.shape,'construction_seconds',time.time()-start,flush=True)
 result={'target':target,'psd_exact_ldl_pivots':pivots,'minorant_exact_bernstein_nodes':uni,'A':[[[str(v)for v in row]for row in a]for a in A],'c':str(c),'h_monomial':[str(H.get((i,0,0),0))for i in range(12)],'residual_monomial':[[list(a),str(v)]for a,v in residual.items()],'bernstein_rounding':'70-bit outward integer coefficient enclosures; floor for residual lower, ceil for Gram upper; midpoint de Casteljau outward','symmetry_domain':'u<=v<=t; F and residual invariant under all six permutations','global':certify(B,G,budget,seconds)}
 dest=Path(__file__).with_name('three_point_d4_exact_'+target.replace('.','_')+'.json');dest.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result['global']),flush=True)
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--target',default='25.733');p.add_argument('--budget',type=int,default=15000);p.add_argument('--seconds',type=int,default=240);args=p.parse_args();run(args.target,args.budget,args.seconds)
