"""Verify the saved exclusion, trusting only rational coefficient strings."""
import json
from pathlib import Path
from fractions import Fraction as F
from math import comb
base=Path(__file__).parent
d=json.loads((base/'pair056_optimized_certificate.json').read_text());a=list(map(F,d['legendre_coefficients']))
assert all(x>=0 for x in a[1:])
def plus(a,b):return [(a[i]if i<len(a)else F(0))+(b[i]if i<len(b)else F(0))for i in range(max(len(a),len(b)))]
def times(a,b):
 c=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
def sc(a,b):return [b*x for x in a]
Ps=[[F(1)],[F(0),F(1)]]
for k in range(2,len(a)):Ps.append(sc(plus(sc([F(0)]+Ps[-1],2*k-1),sc(Ps[-2],1-k)),F(1,k)))
p=[F(0)]
for c,P in zip(a,Ps):p=plus(p,sc(P,c))
B=36*a[0]-F(9,2)*sum(a[1:]);U=F('25.75998653126983156407570227376049402866');gap=U-B
assert str(B)==d['LP_bound'] and str(gap)==d['gap'] and str(U)==d['U']
def check(poly,lo,hi,strict):
 n=len(poly)-1;pw=[F(0)]*(n+1)
 for j,c in enumerate(poly):
  for k in range(j+1):pw[k]+=c*comb(j,k)*(hi-lo)**k*lo**(j-k)
 b=[sum((pw[j]*F(comb(k,j),comb(n,j))for j in range(k+1)),F(0))for k in range(n+1)]
 stack=[(b,0)];count=0
 while stack:
  b,depth=stack.pop();count+=1
  if min(b)>0 if strict else min(b)>=0:continue
  assert depth<40 and count<200000
  row=b[:];left=[row[0]];right=[row[-1]]
  while len(row)>1:row=[(row[j]+row[j+1])/2 for j in range(len(row)-1)];left.append(row[0]);right.append(row[-1])
  stack.extend([(left,depth+1),(right[::-1],depth+1)])
 return count
minorant=check(plus([F(1)],sc(times([F(2),F(-2)],times(p,p)),-1)),F(-1),F(1),False)
q=plus(p,[gap]);exclusion=check(plus([F(1)],sc(times([F(2),F(-2)],times(q,q)),-1)),F(14,25),F(1),True)
print('PASS saved rational coefficients only; independent implementation; minorant nodes',minorant,'exclusion nodes',exclusion)
