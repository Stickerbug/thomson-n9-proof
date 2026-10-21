"""Exact high-degree three-point certificate on the proven competitive domain."""
if not __debug__:
 raise RuntimeError('Certification requires assertions enabled; do not use python -O')
from certify_three_point_d4 import F,add,const,scale,mul,mono,permute,diag,ldl
from certify_conditional_h19 import check
from certify_d4_int64 import split64,safe_array
from exact_tensor_bernstein import coefficients
from pathlib import Path
import json,itertools,time,argparse,runpy

def verify_no_close_triangle(base,U):
 from math import comb
 from certify_rational_lp import add as padd,scale as pscale,mul as pmul
 def nonnegative(q,lo,hi):
  n=len(q)-1;pw=[F(0)]*(n+1)
  for j,c in enumerate(q):
   for k in range(j+1):pw[k]+=c*comb(j,k)*(hi-lo)**k*lo**(j-k)
  b=[sum((pw[j]*F(comb(k,j),comb(n,j))for j in range(k+1)),F(0))for k in range(n+1)];stack=[(b,0)];nodes=0
  while stack:
   b,depth=stack.pop();nodes+=1
   if min(b)>=0:continue
   assert max(b)>0 and depth<50 and nodes<200000,'No nonnegative proof'
   row=b;left=[b[0]];right=[b[-1]]
   while len(row)>1:row=[(row[i]+row[i+1])/2 for i in range(len(row)-1)];left.append(row[0]);right.append(row[-1])
   stack.extend([(left,depth+1),(right[::-1],depth+1)])
  return nodes
 a=[F(x)for x in json.loads((base/'rational_lp24.json').read_text())['legendre_coefficients']];assert all(x>=0 for x in a[1:]);P=[[F(1)],[F(0),F(1)]]
 for k in range(2,len(a)):P.append(pscale(padd(pscale([F(0)]+P[-1],2*k-1),pscale(P[-2],1-k)),F(1,k)))
 p=[F(0)]
 for c,q in zip(a,P):p=padd(p,pscale(q,c))
 lp_nodes=nonnegative(padd([F(1)],pscale(pmul([F(2),F(-2)],pmul(p,p)),-1)),F(-1),F(1))
 h=[F(x)for x in json.loads((base/'conditional_h19_certificate.json').read_text())['h_monomial']]
 hp=check(h,F(-1),F(14,25));hm=check(padd([F(1)],pscale(pmul([F(2),F(-2)],pmul(h,h)),-1)),F(-1),F(14,25))
 B=36*a[0]-F(9,2)*sum(a[1:]);gap=U-B;assert gap>0;defect=padd(h,pscale(p,-1));exclusion=check(padd(defect,[-gap/3]),F(1,2),F(14,25))
 C={(0,0,0):gap}
 for axis in range(3):
  for k,v in enumerate(defect):
   e=[0,0,0];e[axis]=k;e=tuple(e);C[e]=C.get(e,F(0))-v
 C={e:v for e,v in C.items()if v};saved=json.loads((base/'competitive_triple_constraint_certificate.json').read_text());assert saved['domain']==['-1','14/25']and F(saved['gap'])==gap
 assert C=={tuple(e):F(v)for e,v in saved['C_monomial']if F(v)}
 corner=sum(v*F(14,25)**sum(e)for e,v in C.items());assert corner<0 and corner==F(saved['corner_value_exact'])
 return {'status':'exactly_reverified','LP_bound':str(B),'U':str(U),'gap':str(gap),'LP_global_minorant_nodes':lp_nodes,'h19_positive_nodes':hp,'h19_minorant_nodes':hm,'h19_minus_p_gt_gap_over3_nodes':exclusion,'cut':'All actual coordinates >=1/2 impossible for E<=U','normalized_box_cut':'after exact order-cone intersection, 2*l0 >= 2**ds0','proof':'Global p<=f with nonnegative positive-degree Legendre coefficients gives E-B=sum(f-p)+positive moments. For E<=U, every triple sum(f-p)<=gap. h19<=f and h19-p>gap/3 on [1/2,14/25] contradict three close pairs.'}

def verify(path,budget,seconds,out=None):
 start=time.time();path=Path(path);src=json.loads(path.read_text());d=src.get('degree',len(src['A'])-1)
 A=[[[F(v)for v in row]for row in b]for b in src['A']];assert [len(a)for a in A]==list(range(d+1,0,-1))
 piv=[]
 for a in A:
  assert all(len(row)==len(a)for row in a)and all(a[i][j]==a[j][i]for i in range(len(a))for j in range(len(a)))
  piv.append(ldl(a))
 h=list(map(F,src['h_monomial']));lo,hi=F(-1),F(14,25)
 assert check(h,lo,hi)
 # h<=f follows even without sign from (2-2t)*h²<1.
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
    c=A[k][i][j]
    for (a,b,e),v0 in Q[k].items():
     exp=(a+i,b+j,e);kernel[exp]=kernel.get(exp,F(0))+c*v0
 kernel={a:v for a,v in kernel.items()if v};polyF=scale(add(*(permute(kernel,p)for p in itertools.permutations(range(3)))),F(1,6))
 assert all(permute(polyF,p)==polyF for p in itertools.permutations(range(3)))
 if 'F_monomial'in src:assert polyF=={tuple(a):F(v)for a,v in src['F_monomial']if F(v)}
 c=F(src['c']);target=F(src['target']);assert target==12*c-F(3,2)*sum(polyF.values())
 U=F('25.75998653126983156407570227376049402866');assert target<U
 pair_dependency=path.with_name('pair056_optimized_certificate.json')
 assert F(json.loads(pair_dependency.read_text())['U'])==U
 runpy.run_path(str(path.with_name('verify_pair056_saved.py')),run_name='__pair_dependency__')
 close_proof=verify_no_close_triangle(path.parent,U)
 H={(i,0,0):v for i,v in enumerate(h)if v};hs=add(*(permute(H,p)for p in [(0,1,2),(1,0,2),(2,1,0)]))
 R=add(hs,scale(polyF,-7),*(scale(diag(polyF,i),-1)for i in range(3)),const(-c))
 assert R=={tuple(a):F(v)for a,v in src['residual_monomial']if F(v)}
 gram=add(const(1),scale(mul(mul(u,v),t),2),*(scale(mul(x,x),-1)for x in [u,v,t]))
 bits=40;B=safe_array(coefficients(R,[(lo,hi)]*3,bits=bits));G=safe_array(coefficients(gram,[(lo,hi)]*3,bits=bits,upper=True));bounds=[int(B.min()),int(B.max()),int(G.min()),int(G.max())]
 print('PASS exact PSD, minorant, reconstruction, normalization; tensor',B.shape,'construction',time.time()-start,'bounds',bounds,flush=True)
 stack=[(B,G,0,(0,0,0),((-1,1),)*3)];nodes=positive=outside=close_triangle=md=0;walk=time.time()
 while stack and nodes<budget and time.time()-walk<seconds:
  b,g,depth,ds,box=stack.pop();nodes+=1;md=max(md,depth)
  if b.min()>=0:positive+=1;continue
  
  if g.max()<0 or (box[0][0]<<ds[1])>(box[1][1]<<ds[0])or(box[1][0]<<ds[2])>(box[2][1]<<ds[1]):outside+=1;continue
  if 2*box[0][0]>=1<<ds[0]:close_triangle+=1;continue
  assert max(ds)<80,'Unresolved deep box; no certificate'
  axis=min(range(3),key=lambda i:ds[i]);dd=list(ds);dd[axis]+=1;dd=tuple(dd)
  bl,br=split64(b,axis);gl,gr=split64(g,axis,True)
  l,r=box[axis];m=l+r;lb=list(box);rb=list(box);lb[axis]=(2*l,m);rb[axis]=(m,2*r)
  stack.extend([(br,gr,depth+1,dd,tuple(rb)),(bl,gl,depth+1,dd,tuple(lb))])
  if nodes%50000==0:print('progress',nodes,'pending',len(stack),'depth',md,'seconds',time.time()-walk,flush=True)
 result={'status':'certified'if not stack else 'budget_exhausted','target':str(target),'source':str(path.resolve()),'degree':d,'domain':['-1','14/25'],'nodes':nodes,'positive_leaves':positive,'excluded_leaves':outside,'close_triangle_excluded_leaves':close_triangle,'close_triangle_proof':close_proof,'pending':len(stack),'maxdepth':md,'bits':bits,'coefficient_bounds':bounds,'minorant_nodes':minorant,'psd_pivots':piv,'seconds':time.time()-start,'logic':'All arithmetic Fraction or outward integers. Original matrices/rebuilt F/R and lower-bound identity verified. Domain and no-close-triangle pruning are necessary for E<=U by reverified pair056/LP24/h19 proofs. Configurations with E>U automatically exceed target; hence conditional certification implies unconditional lower bound.'}
 dest=Path(out)if out else path.with_name(path.stem+'_competitive_v2_verified.json');assert not dest.exists();dest.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='psd_pivots'}),flush=True)
 return result['status']=='certified'
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('path');p.add_argument('--budget',type=int,default=1500000);p.add_argument('--seconds',type=float,default=120);p.add_argument('--out',required=True);a=p.parse_args();raise SystemExit(0 if verify(a.path,a.budget,a.seconds,a.out)else 2)
