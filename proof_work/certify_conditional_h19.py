"""Discover and exactly certify a conditional degree19 Coulomb minorant."""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json
import numpy as np
from numpy.polynomial import Chebyshev,Polynomial

def plus(a,b):return [(a[i]if i<len(a)else F(0))+(b[i]if i<len(b)else F(0))for i in range(max(len(a),len(b)))]
def times(a,b):
 c=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c

def check(q,lo,hi):
 n=len(q)-1;power=[F(0)]*(n+1)
 for j,c in enumerate(q):
  for k in range(j+1):power[k]+=c*comb(j,k)*(hi-lo)**k*lo**(j-k)
 b=[sum((power[j]*F(comb(k,j),comb(n,j))for j in range(k+1)),F(0))for k in range(n+1)];stack=[(b,0)];nodes=0
 while stack:
  b,d=stack.pop();nodes+=1
  if min(b)>0:continue
  assert max(b)>0 and d<50 and nodes<200000,('no proof',nodes,d)
  row=b;left=[b[0]];right=[b[-1]]
  while len(row)>1:row=[(row[i]+row[i+1])/2 for i in range(len(row)-1)];left.append(row[0]);right.append(row[-1])
  stack.extend([(left,d+1),(right[::-1],d+1)])
 return nodes

def run():
 lo=F(-1);hi=F(14,25);base=Path(__file__).parent
 ch=Chebyshev.interpolate(lambda x:(2-2*x)**(-.5),19,domain=[-1,.56]);p=ch.convert(kind=Polynomial,domain=[-1,1],window=[-1,1])
 for x in [-1,-.4,0,.56]:assert abs(p(x)-ch(x))<1e-10
 h=[F(round(v*10**14),10**14)for v in p.coef];h[0]-=F(1,10**7);eps=F(1,5000000)
 pos=check(h,lo,hi)
 minus=plus([F(1)],[-v for v in times([F(2),F(-2)],times(h,h))]);mnodes=check(minus,lo,hi)
 q=plus(h,[eps]);upper=plus(times([F(2),F(-2)],times(q,q)),[F(-1)]);unodes=check(upper,lo,hi)
 result={'status':'certified','claim':'0<=f(t)-h(t)<1/5000000 for all -1<=t<=14/25','domain':[str(lo),str(hi)],'error_upper':str(eps),'degree':19,'h_monomial':[str(x)for x in h],'positive_nodes':pos,'minorant_nodes':mnodes,'error_nodes':unodes,'logic':'Exact rational Bernstein h>0, 1-(2-2t)h^2>0, (2-2t)(h+eps)^2-1>0. All inequalities cover the whole domain.'}
 dest=base/'conditional_h19_certificate.json';assert not dest.exists();dest.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k]for k in ['status','claim','positive_nodes','minorant_nodes','error_nodes']}),flush=True)
if __name__=='__main__':run()
