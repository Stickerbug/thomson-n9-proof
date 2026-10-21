"""Exact optimized competitive-pair exclusion, E<=U => t<14/25."""
from certify_rational_lp import F,add,scale,mul,comb
from pathlib import Path
import json
base=Path(__file__).parent
proposal=next(r for r in json.loads((base/'optimized_pair_proposals_v2.json').read_text())if r['s']==.56)
a=[F(round(v*10**12),10**12)for v in proposal['a']];a[0]-=F(1,10**6)
assert all(v>=0 for v in a[1:])
Ps=[[F(1)],[F(0),F(1)]]
for k in range(2,len(a)):Ps.append(scale(add(scale([F(0)]+Ps[-1],2*k-1),scale(Ps[-2],1-k)),F(1,k)))
p=[F(0)]
for c,P in zip(a,Ps):p=add(p,scale(P,c))
def prove(q,lo,hi,strict):
 n=len(q)-1;w=hi-lo;power=[F(0)]*(n+1)
 for j,c in enumerate(q):
  for k in range(j+1):power[k]+=c*comb(j,k)*w**k*lo**(j-k)
 b=[sum((power[j]*F(comb(k,j),comb(n,j))for j in range(k+1)),F(0))for k in range(n+1)]
 stack=[(b,0)];count=leaves=maxdepth=0
 while stack:
  b,d=stack.pop();count+=1
  if min(b)>0 if strict else min(b)>=0:leaves+=1;maxdepth=max(maxdepth,d);continue
  assert max(b)>0 and d<40 and count<200000,('failed sufficient test',d,count)
  rows=[b]
  for k in range(n):rows.append([(x+y)/2 for x,y in zip(rows[-1],rows[-1][1:])])
  stack.extend([([r[0]for r in rows],d+1),([r[-1]for r in rows][::-1],d+1)])
 return dict(nodes=count,leaves=leaves,maxdepth=maxdepth)
minorant=prove(add([F(1)],scale(mul([F(2),F(-2)],mul(p,p)),-1)),F(-1),F(1),False)
print('minorant PASS',minorant,flush=True)
B=36*a[0]-F(9,2)*sum(a[1:]);U=F('25.75998653126983156407570227376049402866');gap=U-B
q=add(p,[gap]);exclusion=prove(add([F(1)],scale(mul([F(2),F(-2)],mul(q,q)),-1)),F(14,25),F(1),True)
result={'status':'certified','claim':'Any nine-point Coulomb configuration with E<=U has every distinct pair inner product <14/25=.56.','U':str(U),'LP_bound':str(B),'gap':str(gap),'legendre_coefficients':[str(v)for v in a],'minorant':minorant,'exclusion':exclusion,'logic':'LP defect identity E-B=sum(f-p)+.5 sum_{l>=1} a_l M_l. All terms nonnegative. Squared polynomial cert gives f-p>U-B on [14/25,1), a contradiction for any such pair.'}
(base/'pair056_optimized_certificate.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS',json.dumps({k:result[k]for k in ['status','claim','minorant','exclusion']}),flush=True)
