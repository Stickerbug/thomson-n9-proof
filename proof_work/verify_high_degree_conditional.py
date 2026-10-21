"""Exact high-degree three-point certificate on the proven competitive domain."""
if not __debug__:
 raise RuntimeError('Certification requires assertions enabled; do not use python -O')
from certify_three_point_d4 import F,add,const,scale,mul,mono,permute,diag,ldl
from certify_conditional_h19 import check
from certify_d4_int64 import split64,safe_array
from exact_tensor_bernstein import coefficients
from pathlib import Path
import json,itertools,time,argparse,runpy,hashlib
import numpy as np

def verify(path,budget,seconds,max_axis_depth=80,axis_strategy='balanced',bits=40):
 start=time.time();path=Path(path);src=json.loads(path.read_text());d=src.get('degree',len(src['A'])-1)
 model_hash=hashlib.sha256(path.read_bytes()).hexdigest()
 A=[[[F(v)for v in row]for row in b]for b in src['A']];assert [len(a)for a in A]==list(range(d+1,0,-1))
 piv=[]
 for a in A:
  assert all(len(row)==len(a)for row in a)and all(a[i][j]==a[j][i]for i in range(len(a))for j in range(len(a)))
  piv.append(ldl(a))
 h=list(map(F,src['h_monomial']));lo,hi=F(-1),F(14,25)
 assert check(h,lo,hi)
 def conv(a,b):
  o=[F(0)]*(len(a)+len(b)-1)
  for i,x in enumerate(a):
   for j,y in enumerate(b):o[i+j]+=x*y
  return o
 sq=conv([F(2),F(-2)],conv(h,h));q=[-v for v in sq];q[0]+=1;minorant=check(q,lo,hi)
 u,v,t=(mono(i,1)for i in range(3));aa=add(t,scale(mul(u,v),-1));bb=mul(add(const(1),scale(mul(u,u),-1)),add(const(1),scale(mul(v,v),-1)))
 Q=[const(1),aa]
 for k in range(1,d):Q.append(add(scale(mul(aa,Q[-1]),2),scale(mul(bb,Q[-2]),-1)))
 kernel={}
 for k in range(d+1):
  for i in range(d+1-k):
   for j in range(d+1-k):
    for (a,b,e),v0 in Q[k].items():
     exp=(a+i,b+j,e);kernel[exp]=kernel.get(exp,F(0))+A[k][i][j]*v0
 kernel={a:v for a,v in kernel.items()if v};polyF=scale(add(*(permute(kernel,p)for p in itertools.permutations(range(3)))),F(1,6))
 assert all(permute(polyF,p)==polyF for p in itertools.permutations(range(3)))
 if 'F_monomial'in src:assert polyF=={tuple(a):F(v)for a,v in src['F_monomial']if F(v)}
 c=F(src['c']);target=F(src['target']);assert target==12*c-F(3,2)*sum(polyF.values())
 U=F('25.75998653126983156407570227376049402866');assert target<U
 pair_dependency=path.with_name('pair056_optimized_certificate.json')
 assert F(json.loads(pair_dependency.read_text())['U'])==U
 runpy.run_path(str(path.with_name('verify_pair056_saved.py')),run_name='__pair_dependency__')
 H={(i,0,0):v for i,v in enumerate(h)if v};hs=add(*(permute(H,p)for p in [(0,1,2),(1,0,2),(2,1,0)]))
 R=add(hs,scale(polyF,-7),*(scale(diag(polyF,i),-1)for i in range(3)),const(-c))
 assert R=={tuple(a):F(v)for a,v in src['residual_monomial']if F(v)}
 gram=add(const(1),scale(mul(mul(u,v),t),2),*(scale(mul(x,x),-1)for x in [u,v,t]))
 B=safe_array(coefficients(R,[(lo,hi)]*3,bits=bits));G=safe_array(coefficients(gram,[(lo,hi)]*3,bits=bits,upper=True));bounds=[int(B.min()),int(B.max()),int(G.min()),int(G.max())]
 print('PASS exact PSD, minorant, reconstruction, normalization; tensor',B.shape,'construction',time.time()-start,'bounds',bounds,flush=True)
 stack=[(B,G,0,(0,0,0),((-1,1),)*3)];nodes=positive=outside=md=0;walk=time.time();depth_limited=False
 while stack and nodes<budget and time.time()-walk<seconds:
  b,g,depth,ds,box=stack.pop();nodes+=1;md=max(md,depth)
  if b.min()>=0:positive+=1;continue
  if g.max()<0 or (box[0][0]<<ds[1])>(box[1][1]<<ds[0])or(box[1][0]<<ds[2])>(box[2][1]<<ds[1]):outside+=1;continue
  if max(ds)>=max_axis_depth:
   stack.append((b,g,depth,ds,box));depth_limited=True;break
  if axis_strategy=='balanced':
   axis=min(range(3),key=lambda i:ds[i])
  else:
   scores=[int(np.max(np.abs(np.diff(b,axis=i)))) for i in range(3)]
   axis=max(range(3),key=lambda i:scores[i])
   if axis_strategy=='adaptive' and max(scores)<=8: axis=min(range(3),key=lambda i:ds[i])
  dd=list(ds);dd[axis]+=1;dd=tuple(dd)
  bl,br=split64(b,axis);gl,gr=split64(g,axis,True)
  l,r=box[axis];m=l+r;lb=list(box);rb=list(box);lb[axis]=(2*l,m);rb[axis]=(m,2*r)
  stack.extend([(br,gr,depth+1,dd,tuple(rb)),(bl,gl,depth+1,dd,tuple(lb))])
  if nodes%50000==0:print('progress',nodes,'pending',len(stack),'depth',md,'seconds',time.time()-walk,flush=True)
 status='certified'if not stack else ('unresolved_depth_limit'if depth_limited else 'budget_exhausted')
 result={'status':status,'target':str(target),'source':str(path.resolve()),'model_sha256':model_hash,'degree':d,'domain':['-1','14/25'],'nodes':nodes,'positive_leaves':positive,'excluded_leaves':outside,'pending':len(stack),'maxdepth':md,'bits':bits,'max_axis_depth':max_axis_depth,'axis_strategy':axis_strategy,'coefficient_bounds':bounds,'minorant_nodes':minorant,'psd_pivots':piv,'seconds':time.time()-start,'logic':'Exact Fraction and outward integer arithmetic. The search starts from the full root box; a lower bound is accepted only when its complete tree closes. Competitive configurations lie in this domain by the independently checked pair exclusion.'}
 if stack:
  frontier={'model_sha256':model_hash,'degree':d,'bits':bits,'frontier':[{'B':b.tolist(),'G':g.tolist(),'depth':depth,'ds':list(ds),'box':[list(x)for x in box]}for b,g,depth,ds,box in stack]}
  fp=path.with_name(path.stem+'_frontier.json');assert not fp.exists();fp.write_text(json.dumps(frontier,separators=(',',':'))+'\n');result['frontier_file']=str(fp.resolve())
 dest=path.with_name(path.stem+'_result.json');assert not dest.exists();dest.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
 return result['status']=='certified'
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('path');p.add_argument('--budget',type=int,default=1500000);p.add_argument('--seconds',type=float,default=600);p.add_argument('--max-axis-depth',type=int,default=80);p.add_argument('--axis-strategy',choices=['balanced','slope','adaptive'],default='balanced');p.add_argument('--bits',type=int,default=40);a=p.parse_args();raise SystemExit(0 if verify(a.path,a.budget,a.seconds,a.max_axis_depth,a.axis_strategy,a.bits)else 2)
