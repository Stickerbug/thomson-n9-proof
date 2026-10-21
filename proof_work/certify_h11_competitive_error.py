"""Exact rational error bound for saved h on competitive inner-product domain."""
from certify_rational_lp import F,add,scale,mul,comb
from pathlib import Path
import json
base=Path(__file__).parent
H=list(map(F,json.loads((base/'three_point_d4_exact_25_745.json').read_text())['h_monomial']))
EPS=F(3,10000)
p=add(H,[EPS])
R=add(mul([F(2),F(-2)],mul(p,p)),[F(-1)])
lo=F(-1);hi=F(57,100);width=hi-lo;n=len(R)-1
power=[F(0)]*(n+1)
for j,c in enumerate(R):
 for k in range(j+1):power[k]+=c*comb(j,k)*width**k*lo**(j-k)
b=[sum((power[j]*F(comb(k,j),comb(n,j))for j in range(k+1)),F(0))for k in range(n+1)]
stack=[(b,0)];leaves=0;depthmax=0;nodes=0
while stack:
 b,depth=stack.pop();nodes+=1
 if min(b)>0:
  leaves+=1;depthmax=max(depthmax,depth);continue
 assert max(b)>0 and depth<40,('cannot certify',depth)
 rows=[b]
 for k in range(n):rows.append([(x+y)/2 for x,y in zip(rows[-1],rows[-1][1:])])
 stack.extend([([row[0]for row in rows],depth+1),([row[-1]for row in rows][::-1],depth+1)])
# Previously certified h>0 and h<=f; R>0 => h+EPS>f on the restricted domain.
# Verify positivity of h+EPS afresh using its Bernstein coefficients as well.
m=len(p)-1;pw=[F(0)]*(m+1)
for j,c in enumerate(p):
 for k in range(j+1):pw[k]+=c*comb(j,k)*width**k*lo**(j-k)
bp=[sum((pw[j]*F(comb(k,j),comb(m,j))for j in range(k+1)),F(0))for k in range(m+1)]
assert min(bp)>0
result={'claim':'For every -1<=t<=57/100, f(t)-h(t)<3/10000, for the saved rational h. Lower error >=0 follows from the prior full-domain minorant certificate.','epsilon':str(EPS),'positive_bernstein_leaves':leaves,'nodes':nodes,'max_depth':depthmax,'arithmetic':'Exact Fraction throughout'}
(base/'h11_competitive_error_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS:',json.dumps(result))
