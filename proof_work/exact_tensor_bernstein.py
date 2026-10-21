"""Exact multivariate monomial-to-Bernstein transform by integer tensor contractions."""
from fractions import Fraction as F
from math import comb,lcm
import numpy as np

def coefficients(poly,box,degrees=None,bits=48,upper=False):
 dim=len(box);deg=degrees or tuple(max((a[i]for a in poly),default=0)for i in range(dim));assert len(deg)==dim
 denom=1
 for v in poly.values():denom=lcm(denom,F(v).denominator)
 C=np.zeros(tuple(n+1 for n in deg),dtype=object)
 for a,v in poly.items():v=F(v);C[a]=v.numerator*(denom//v.denominator)
 for axis,(lo,hi)in enumerate(box):
  lo,hi=F(lo),F(hi);n=deg[axis];width=hi-lo
  T=[[sum((F(comb(i,j))*lo**(i-j)*width**j*F(comb(k,j),comb(n,j))for j in range(min(i,k)+1)),F(0))for i in range(n+1)]for k in range(n+1)]
  td=1
  for row in T:
   for v in row:td=lcm(td,v.denominator)
  Ti=np.array([[v.numerator*(td//v.denominator)for v in row]for row in T],dtype=object)
  W=np.moveaxis(C,axis,0);shape=W.shape
  W=(Ti@W.reshape(n+1,-1)).reshape(shape);C=np.moveaxis(W,0,axis);denom*=td
 scale=1<<bits
 if upper:C=np.array([-((-int(v)*scale)//denom)for v in C.flat],dtype=object).reshape(C.shape)
 else:C=np.array([(int(v)*scale)//denom for v in C.flat],dtype=object).reshape(C.shape)
 return C
