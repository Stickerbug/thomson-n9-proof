"""Check interval enclosure against independent exact Fraction endpoint arithmetic."""
from fractions import Fraction as F
import random
from dyadic_interval import I,S
rng=random.Random(916)
checks=0
for trial in range(500):
    a,b=sorted(F(rng.randint(-1000,1000),rng.randint(1,300)) for _ in range(2))
    c,d=sorted(F(rng.randint(-1000,1000),rng.randint(1,300)) for _ in range(2))
    A,B=I(a,b),I(c,d)
    def check(C,values):
        global checks
        assert F(C.lo,S)<=min(values) and F(C.hi,S)>=max(values)
        checks+=1
    check(A+B,[a+c,b+d]);check(A-B,[a-d,b-c])
    check(A*B,[a*c,a*d,b*c,b*d])
    if c*d>0:check(A/B,[a/c,a/d,b/c,b/d])
    if a>=0:
        C=A.sqrt()
        assert C.lo>=0 and F(C.lo,S)**2<=a and F(C.hi,S)**2>=b
        checks+=1
print('PASS:',checks,'independent exact-rational enclosure checks')
