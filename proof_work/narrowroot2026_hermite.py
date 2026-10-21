if not __debug__:
 raise RuntimeError('Run without -O')
"""Certified Hermite contact minorant with positive Stieltjes remainder factor.
Exact root interval and dyadic operations; supplementary nodes are explicit rationals.
"""
from pathlib import Path
from fractions import Fraction as F
import json
from dyadic_interval import I,S
from certify_pair_moments import derivative
rootinfo=json.loads(Path(__file__).with_name('narrowroot2026_root.json').read_text());L,U=rootinfo['root_refined']

def square(x):
 lo=0 if x.lo<=0<=x.hi else min(x.lo*x.lo,x.hi*x.hi)//S
 hi=-((-max(x.lo*x.lo,x.hi*x.hi))//S)
 return I(lo,hi,raw=True)
def run(extra=()):
 assert derivative(I(L)).hi<0<derivative(I(U)).lo
 r=I(L,U);nodes=[r*r/2-1,-r,I('-0.5'),2*r*r-1,1-I('1.5')*r*r,r/2]+[I(q)for q in extra]
 nodes.sort(key=lambda z:z.lo)
 assert all(a.hi<b.lo for a,b in zip(nodes,nodes[1:]))
 z=[v for v in nodes for _ in range(2)]
 f=lambda t:1/(2-2*t).sqrt()
 tab=[f(t)for t in z];coeff=[tab[0]]
 for j in range(1,len(z)):
  nxt=[]
  for i in range(j,len(z)):
   if j==1 and i%2==1:
    nxt.append(1/((2-2*z[i])**3).sqrt())
   else:nxt.append((tab[i-j+1]-tab[i-j])/(z[i]-z[i-j]))
  tab=nxt;coeff.append(tab[0])
 def H(t):
  val=coeff[-1]
  for j in range(len(coeff)-2,-1,-1):val=coeff[j]+(t-z[j])*val
  return val
 def omega(t):
  val=I(1)
  for node in nodes:val=val*square(t-node)
  return val
 left,right=I('-1.01'),I('.57')
 kl=(f(left)-H(left))/omega(left);ku=(f(right)-H(right))/omega(right)
 assert kl.lo>0 and ku.lo>0
 # For t in [-1,.56], kl <= K(t) <= ku by the exact Stieltjes formula.
 maximum=0;N=4096
 for i in range(N):
  t=I(F(-1)+F(39*i,25*N),F(-1)+F(39*(i+1),25*N))
  maximum=max(maximum,omega(t).hi)
 bound=ku*I(0,maximum,raw=True)
 return {'degree':len(coeff)-1,'supplementary_nodes':[str(q)for q in extra],'newton_nodes':[n.bounds()for n in z],'newton_coefficients':[c.bounds()for c in coeff],'K_lower':kl.bounds(),'K_upper':ku.bounds(),'omega_upper_numerator':str(maximum),'scale_bits':384,'uniform_error_upper':bound.bounds(),'whole_interval_boxes':N,'error_display':float(F(bound.hi,S))}
if __name__=='__main__':
 cases=[run(),run([F(-1),F(-9,10),F(-2,5),F(-1,5),F(1,10),F(9,20),F(13,25),F(14,25)])]
 assert int(cases[1]['uniform_error_upper']['hi_numerator']) < I(F(3,2*10**9)).lo
 result={'status':'certified_contact_minorant_and_error_bound','domain':['-1','14/25'],'scope':'For true r_star, Hermite H matches f,f-prime at all six candidate nodes and supplementary nodes. f-H=omega*K with 0<K_lower<=K<=K_upper. This is not a Thomson global bound; no kernel nonnegativity is claimed.','cases':cases}
 out=Path(__file__).with_name('narrowroot2026_hermite.json')
 if out.exists():assert json.loads(out.read_text())==result
 else:out.write_text(json.dumps(result,indent=2)+'\n')
 for c in cases:print('degree',c['degree'],'certified contact minorant; uniform error upper',c['error_display'])
