"""Symbolic Gram-boundary geometry; necessary sharp residual conditions only."""
from pathlib import Path
import json
import sympy as s
r=s.symbols('r',positive=True);u,v,t=s.symbols('u v t');x=s.Matrix([u,v,t])
g=1+2*u*v*t-u*u-v*v-t*t
grad=s.Matrix([s.diff(g,z)for z in x]);H=s.hessian(g,x)
C=r*r/2-1;B=2*r*r-1
cases=[('C', [C,r/2,r/2],(1-C)*s.Matrix([1,-r,-r]),s.Matrix([[0,2*r],[1,1],[-1,1]]),s.diag(-2*r*r,2*r*r-8)),('B',[-r,-r,B],(1-B)*s.Matrix([2*r,2*r,1]),s.Matrix([[1,1],[-1,1],[0,-4*r]]),s.diag(-8*r*r,8*r*r-8)),('equilateral',[-s.Rational(1,2)]*3,s.Matrix([s.Rational(3,2)]*3),s.Matrix([[1,1],[-1,1],[0,-2]]),s.diag(-2,-6))]
rows=[]
for name,point,normal,T,expected in cases:
 sub=dict(zip(x,point));n=grad.subs(sub);hg=H.subs(sub)
 assert s.simplify(g.subs(sub))==0
 assert all(s.simplify(z)==0 for z in n-normal)
 assert all(s.simplify(z)==0 for z in T.T*n)
 assert all(s.simplify(z)==0 for z in T.T*hg*T-expected)
 rows.append({'type':name,'point':[str(z)for z in point],'gradient':[str(s.expand(z))for z in normal],'tangent_basis':[[str(z)for z in row]for row in T.tolist()],'projected_gram_hessian':[[str(z)for z in row]for row in expected.tolist()]})
out={'status':'symbolically_verified_geometry','scope':'For any smooth symmetric residual R>=0 on g>=0 with R=0 at these candidate boundary triples, gradR=lambda*gradg with lambda>=0 and T^T(HessR-lambda*Hessg)T>=0. Applies to true r_star in (0,1); no approximate-radius transfer. Not a global Thomson proof.','cases':rows}
p=Path(__file__).with_name('boundary_sharp_geometry_v1.json')
if p.exists():assert json.loads(p.read_text())==out
else:p.write_text(json.dumps(out,indent=2)+'\n')
print('PASS: three boundary triples, normals, tangent bases and curvature corrections symbolically verified.')
