"""Exact binomial-coefficient reference for the object de Casteljau implementation."""
if not __debug__:
 raise RuntimeError('Assertions must be active')
from verify_d10_object70_sym_fast_v2 import split_fast
import numpy as np
from fractions import Fraction as F
from math import comb
import random,json
rng=random.Random(7592);checks=0
for shape,repeats in [((3,4,5),24),((21,2,2),3)]:
 for test in range(repeats):
  a=np.array([rng.randrange(-(1<<90),1<<90)for _ in range(int(np.prod(shape)))],dtype=object).reshape(shape)
  for axis in range(3):
   q=np.moveaxis(a,axis,0);n=q.shape[0]-1
   for upper in [False,True]:
    lo,hi=split_fast(a,axis,upper=upper);lo=np.moveaxis(lo,axis,0);hi=np.moveaxis(hi,axis,0)
    for j in range(n+1):
     for idx in np.ndindex(q.shape[1:]):
      vl=sum((F(comb(j,k))*q[(k,)+idx]for k in range(j+1)),F(0))/(1<<j)
      vr=sum((F(comb(n-j,k))*q[(j+k,)+idx]for k in range(n-j+1)),F(0))/(1<<(n-j))
      rnd=lambda x:-((-x.numerator)//x.denominator)if upper else x.numerator//x.denominator
      assert lo[(j,)+idx]==rnd(vl)and hi[(j,)+idx]==rnd(vr);checks+=2
print(json.dumps({'status':'PASS','reference':'explicit binomial Fraction Bernstein half-transform','coefficient_checks':checks,'signed_input_bits':90,'seed':7592}))
