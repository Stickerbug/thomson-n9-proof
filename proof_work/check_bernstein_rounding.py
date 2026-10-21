"""Independent Fraction endpoint audit of tensor integer Bernstein rounding."""
from fractions import Fraction as F
import numpy as np
from certify_three_point_d4 import bernstein,split
from math import comb
from random import Random
rng=Random(90107)
checks=0
for trial in range(20):
    deg=(3,2,2)
    poly={a:F(rng.randint(-30,30),rng.randint(1,31))for a in np.ndindex(4,3,3)}
    # independently evaluate degree-elevated Bernstein function enclosure at random rational points
    low=bernstein(poly,degrees=deg,bits=70)
    high=bernstein(poly,degrees=deg,bits=70,upper=True)
    for attempt in range(10):
        x=[F(rng.randint(0,30),30)for _ in range(3)]
        value=sum(c*(2*x[0]-1)**a[0]*(2*x[1]-1)**a[1]*(2*x[2]-1)**a[2]for a,c in poly.items())
        basis=lambda a: np.prod([F(comb(d,j))*z**j*(1-z)**(d-j)for d,j,z in zip(deg,a,x)])
        L=sum(F(low[a],1<<70)*basis(a)for a in np.ndindex(low.shape))
        U=sum(F(high[a],1<<70)*basis(a)for a in np.ndindex(high.shape))
        assert L<=value<=U
        checks+=1
    for axis in range(3):
        LL,LR=split(low,axis);UL,UR=split(high,axis,upper=True)
        # independently perform exact rational de Casteljau on the lower/upper coefficient tensors
        for source,actuals,is_upper in [(low,(LL,LR),False),(high,(UL,UR),True)]:
            work=np.moveaxis(source,axis,0).copy();work=np.array([F(v,1<<70)for v in work.flat],dtype=object).reshape(work.shape)
            n=len(work)-1;l=np.empty_like(work);r=np.empty_like(work);l[0]=work[0];r[n]=work[n]
            for k in range(1,n+1):
                work=(work[:-1]+work[1:])/2;l[k]=work[0];r[n-k]=work[-1]
            for actual,exact in zip(actuals,(np.moveaxis(l,0,axis),np.moveaxis(r,0,axis))):
                for av,ev in zip(actual.flat,exact.flat):
                    assert (F(av,1<<70)>=ev) if is_upper else (F(av,1<<70)<=ev)
                    checks+=1
print('PASS:',checks,'independent exact Fraction tensor Bernstein and split checks')
