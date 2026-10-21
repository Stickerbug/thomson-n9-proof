"""Independent rational/dual-number checks of local verification components."""
from pathlib import Path
from fractions import Fraction as Q
from math import comb,isqrt,prod
import json
import independent_local_arithmetic as m
from independent_integer_interval import Box,InvalidMath
class D2:
    def __init__(self,v,g=None,h=None):self.v=Q(v);self.g=[Q(0)]*2 if g is None else g;self.h=[[Q(0)]*2 for _ in range(2)]if h is None else h
    def cast(v):return v if isinstance(v,D2)else D2(v)
    def __add__(a,b):
        b=D2.cast(b);return D2(a.v+b.v,[a.g[i]+b.g[i]for i in range(2)],[[a.h[i][j]+b.h[i][j]for j in range(2)]for i in range(2)])
    __radd__=__add__
    def __neg__(a):return D2(-a.v,[-x for x in a.g],[[-x for x in row]for row in a.h])
    def __sub__(a,b):return a+-D2.cast(b)
    def __rsub__(a,b):return D2.cast(b)+-a
    def __mul__(a,b):
        b=D2.cast(b);return D2(a.v*b.v,[a.g[i]*b.v+a.v*b.g[i]for i in range(2)],[[a.h[i][j]*b.v+a.g[i]*b.g[j]+a.g[j]*b.g[i]+a.v*b.h[i][j]for j in range(2)]for i in range(2)])
    __rmul__=__mul__
    def sqrt(a):
        n=isqrt(a.v.numerator);d=isqrt(a.v.denominator);assert n*n==a.v.numerator and d*d==a.v.denominator;s=Q(n,d);return D2(s,[x/(2*s)for x in a.g],[[a.h[i][j]/(2*s)-a.g[i]*a.g[j]/(4*s**3)for j in range(2)]for i in range(2)])
def contains(x,q):assert x.lo<=q<=x.hi,(x.serial(),str(q))
def exact(poly,point,diff=(0,0,0)):
    total=Q(0)
    for ex,value in poly.items():
        if any(ex[i]<diff[i]for i in range(3)):continue
        for i in range(3):value*=prod(range(ex[i]-diff[i]+1,ex[i]+1))*point[i]**(ex[i]-diff[i])
        total+=value
    return total
def main():
    poly={(4,1,0):Q(3,7),(0,2,3):Q(-5,11),(1,1,1):Q(7,13),(0,0,0):Q(2)};center=[Q(1,4),Q(-2,3),Q(3,5)];shifted=m.shift({e:Box(v)for e,v in poly.items()},list(map(Box,center)));closed={}
    for ex,value in poly.items():
        for i in range(ex[0]+1):
            for j in range(ex[1]+1):
                for k in range(ex[2]+1):
                    out=(i,j,k);closed[out]=closed.get(out,Q(0))+value*prod(comb(ex[a],out[a])*center[a]**(ex[a]-out[a])for a in range(3))
    assert set(shifted)==set(closed)
    for e,v in shifted.items():contains(v,closed[e])
    point=[Q(3,7),Q(-1,5),Q(2,9)];grad,H=m.jet(shifted,[Box(x-c)for x,c in zip(point,center)])
    for i in range(3):
        diff=[0]*3;diff[i]+=1;contains(grad[i],exact(poly,point,diff))
        for j in range(3):diff2=diff[:];diff2[j]+=1;contains(H[i][j],exact(poly,point,diff2))
    points=[(Q(0),Q(0)),(Q(3,5),Q(4,5)),(Q(-3,5),Q(-3,5)),(Q(-1,2),Q(-1,2))]
    for v,t in points:
        V=D2(v,[Q(1),Q(0)]);T=D2(t,[Q(0),Q(1)]);B=V*T-((1-V*V)*(1-T*T)).sqrt();b,db,ddb,s=m.graph(Box(v),Box(t));contains(b,B.v)
        for i in range(2):
            contains(db[i],B.g[i])
            for j in range(2):contains(ddb[i][j],B.h[i][j])
        # Full chain-rule check on the synthetic R(u,v,t)=u^2+uv+3vt+t^2.
        G=B*B+B*V+3*V*T+T*T;Rgrad=[2*b+Box(v),b+3*Box(t),3*Box(v)+2*Box(t)];RH=[[Box(2),Box(1),Box(0)],[Box(1),Box(0),Box(3)],[Box(0),Box(3),Box(2)]];GH=m.graph_hessian(Rgrad,RH,db,ddb)
        for i in range(2):
            for j in range(2):contains(GH[i][j],G.h[i][j])
    negatives=[]
    cases=[('W_nonunit',lambda:m.rational_unit_lower([[2,0],[0,1]],2)),('W_upper_nonzero',lambda:m.rational_unit_lower([[1,1],[0,1]],2)),('W_wrong_dimension',lambda:m.rational_unit_lower([[1]],2)),('negative_LDL',lambda:m.ldl([[Box(-1),Box(0)],[Box(0),Box(1)]])),('zero_LDL',lambda:m.ldl([[Box(1),Box(0)],[Box(0),Box(0)]])),('graph_pole',lambda:m.graph(Box(1),Box(0)))]
    for name,call in cases:
        try:call()
        except InvalidMath as exc:negatives.append({'case':name,'status':'REJECTED_MATHEMATICALLY','reason':str(exc)})
        else:raise AssertionError(name)
    result={'status':'INDEPENDENT_LOCAL_COMPONENT_TESTS_PASS','translated_polynomial_coefficients_checked':len(closed),'derivative_interchecks':'all3gradient+9Hessian entries against direct Fraction monomial derivatives','graph_interchecks':'closed graph value/gradient/Hessian against independent exact Fraction second-order dual arithmetic at4rational radical-square points','graph_chainrule_interchecks':'full pulledback synthetic polynomial Hessian against dual arithmetic at4points','negative_tests':negatives}
    with Path(__file__).with_name('independent_local_component_tests.json').open('x')as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps(result),flush=True)
if __name__=='__main__':main()
