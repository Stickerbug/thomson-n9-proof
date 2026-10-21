"""Independent signed-integer implementation of outward 640-bit intervals."""
from fractions import Fraction as Q
from math import isqrt
BITS=640
S=1<<BITS
class InvalidMath(ValueError):pass
class Box:
    def __init__(self,lo,hi=None,raw=False):
        if raw:self.l,self.h=lo,hi
        else:
            if isinstance(lo,Box)and hi is None:self.l,self.h=lo.l,lo.h;return
            lo=Q(lo);hi=lo if hi is None else Q(hi)
            if lo>hi:raise InvalidMath('reversed interval before rounding')
            self.l=(lo.numerator*S)//lo.denominator;self.h=-((-hi.numerator*S)//hi.denominator)
        if self.l>self.h:raise InvalidMath('reversed interval')
    @property
    def lo(self):return Q(self.l,S)
    @property
    def hi(self):return Q(self.h,S)
    @staticmethod
    def cast(x):return x if isinstance(x,Box)else Box(x)
    def __add__(self,x):
        x=self.cast(x);return Box(self.l+x.l,self.h+x.h,True)
    __radd__=__add__
    def __neg__(self):return Box(-self.h,-self.l,True)
    def __sub__(self,x):return self+-self.cast(x)
    def __rsub__(self,x):return self.cast(x)+-self
    def __mul__(self,x):
        x=self.cast(x);v=(self.l*x.l,self.l*x.h,self.h*x.l,self.h*x.h);return Box(min(v)//S,-((-max(v))//S),True)
    __rmul__=__mul__
    def reciprocal(self):
        if self.l<=0<=self.h:raise InvalidMath('reciprocal interval crosses zero')
        return Box((S*S)//self.h,-((-(S*S))//self.l),True)
    def __truediv__(self,x):return self*self.cast(x).reciprocal()
    def __rtruediv__(self,x):return self.cast(x)*self.reciprocal()
    def __pow__(self,n):
        if type(n)is not int or n<0:raise InvalidMath('nonnegative integer exponent required')
        out=Box(1)
        for _ in range(n):out=out*self
        return out
    def sqrt(self):
        if self.l<0:raise InvalidMath('negative sqrt input')
        l=isqrt(self.l*S);h=isqrt(self.h*S)
        if h*h<self.h*S:h+=1
        if not(l*l<=self.l*S and h*h>=self.h*S):raise InvalidMath('sqrt enclosure failed')
        return Box(l,h,True)
    def serial(self):return [str(self.lo),str(self.hi)]
