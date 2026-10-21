"""Outward-rounded dyadic intervals using Python integers only.
Every bound is an exact rational with denominator 2**BITS.
No floating point is used in certificate computations.
"""
from math import isqrt
from fractions import Fraction
BITS=384
S=1 << BITS

def ceildiv(a,b):
    return -((-a)//b)

class I:
    __slots__=('lo','hi')
    def __init__(self,lo,hi=None,raw=False):
        if raw:
            self.lo,self.hi=lo,lo if hi is None else hi
        else:
            a=Fraction(lo); b=a if hi is None else Fraction(hi)
            self.lo=(a.numerator*S)//a.denominator
            self.hi=ceildiv(b.numerator*S,b.denominator)
        assert self.lo<=self.hi
    @staticmethod
    def cast(x): return x if isinstance(x,I) else I(x)
    def __add__(self,b):
        b=I.cast(b); return I(self.lo+b.lo,self.hi+b.hi,raw=True)
    __radd__=__add__
    def __neg__(self): return I(-self.hi,-self.lo,raw=True)
    def __sub__(self,b): return self+-I.cast(b)
    def __rsub__(self,b): return I.cast(b)+-self
    def __mul__(self,b):
        b=I.cast(b); v=[self.lo*b.lo,self.lo*b.hi,self.hi*b.lo,self.hi*b.hi]
        return I(min(v)//S,ceildiv(max(v),S),raw=True)
    __rmul__=__mul__
    def reciprocal(self):
        assert self.lo*self.hi>0, 'division interval contains zero'
        return I((S*S)//self.hi,ceildiv(S*S,self.lo),raw=True)
    def __truediv__(self,b): return self*I.cast(b).reciprocal()
    def __rtruediv__(self,b): return I.cast(b)*self.reciprocal()
    def sqrt(self):
        assert self.lo>=0
        a=isqrt(self.lo*S); b=isqrt(self.hi*S)
        if b*b<self.hi*S: b+=1
        return I(a,b,raw=True)
    def __pow__(self,n):
        assert isinstance(n,int) and n>=0
        if n==0:return I(1)
        if n==1:return self
        a=self**(n//2); a=a*a
        return a if n%2==0 else a*self
    def bounds(self):
        return {'lo_numerator':str(self.lo),'hi_numerator':str(self.hi),'denominator_power_of_two':BITS}
    def pretty(self):
        from decimal import Decimal, localcontext
        with localcontext() as c:
            c.prec=28
            return [str(Decimal(self.lo)/Decimal(S)),str(Decimal(self.hi)/Decimal(S))]
