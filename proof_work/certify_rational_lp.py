"""Verify an exact GLOBAL Thomson N9 lower bound with rational arithmetic."""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json

def add(a,b):
    return [(a[i] if i<len(a) else F(0))+(b[i] if i<len(b) else F(0)) for i in range(max(len(a),len(b)))]
def scale(a,s): return [v*s for v in a]
def mul(a,b):
    out=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out

def run():
    path=Path(__file__).with_name('rational_lp24.json')
    a=list(map(F,json.loads(path.read_text())['legendre_coefficients']))
    assert all(v>=0 for v in a[1:])
    polynomials=[[F(1)],[F(0),F(1)]]
    for k in range(2,len(a)):
        polynomials.append(scale(add(scale([F(0)]+polynomials[-1],2*k-1),scale(polynomials[-2],1-k)),F(1,k)))
    p=[F(0)]
    for c,P in zip(a,polynomials):p=add(p,scale(P,c))
    # R(t)=1-(2-2t)p(t)^2. R>=0 implies |p|<=f and hence p<=f.
    R=add([F(1)],scale(mul([F(2),F(-2)],mul(p,p)),-1))
    n=len(R)-1
    # Change t=2x-1, x in [0,1].
    power=[F(0)]*(n+1)
    for j,c in enumerate(R):
        for k in range(j+1):power[k]+=c*comb(j,k)*2**k*(-1)**(j-k)
    bernstein=[sum((power[j]*F(comb(k,j),comb(n,j)) for j in range(k+1)),F(0)) for k in range(n+1)]
    stack=[(bernstein,0)];leaves=0;maxdepth=0
    while stack:
        b,depth=stack.pop()
        if min(b)>=0:
            leaves+=1;maxdepth=max(maxdepth,depth);continue
        assert max(b)>0, 'Negative subinterval disproves sufficient squared minorant test'
        assert depth<35, 'Subdivision depth limit reached'
        rows=[b]
        for k in range(n):rows.append([(u+v)/2 for u,v in zip(rows[-1],rows[-1][1:])])
        left=[row[0] for row in rows]
        right=[row[-1] for row in rows][::-1]
        stack.extend([(left,depth+1),(right,depth+1)])
    B=36*a[0]-F(9,2)*sum(a[1:])
    assert B>F('25.7293')
    result={'exact_global_lower_bound':str(B),'display_only':float(B),'bernstein_leaves':leaves,'maximum_depth':maxdepth,'claim':'Every nine-point unit-sphere Coulomb configuration has energy >= exact_global_lower_bound.'}
    out=Path(__file__).with_name('rational_lp_certificate.json')
    if not out.exists():out.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: all positive-degree Legendre coefficients nonnegative.')
    print('PASS: R=1-(2-2t)p^2 >=0 on [-1,1] by exact Bernstein subdivision:',leaves,'leaves, max depth',maxdepth)
    print('GLOBAL lower bound:',B,'approximately',float(B))
    return result

if __name__=='__main__':run()
