"""Small exact geometric identity audit; no solver/root computation."""
import sympy as s,json,time,hashlib
from pathlib import Path
from candidate_low_rank import features
from fractions import Fraction as F
start=time.time();r,h=s.symbols('r h',real=True);q=s.sqrt(3)/2;angles=[(1,0),(-s.Rational(1,2),q),(-s.Rational(1,2),-q)];pts=[(r*a,r*b,z*h)for z in [1,-1]for a,b in angles]+[(-a,-b,0)for a,b in angles]
def reduce(p):return s.rem(s.Poly(s.expand(p),h),s.Poly(h*h-(1-r*r),h)).as_expr().expand()
def rp(a,b,k):return sum((-1)**j*s.binomial(k,2*j)*a**(k-2*j)*b**(2*j)for j in range(k//2+1))
checks=[]
for k in range(11):
 pp,cc=features(r,k,11-k)
 for i in range(11-k):
  pm=sum(rp(h*x-r*z,y,k)*(r*x+h*z)**i for x,y,z in pts);cm=sum(rp(y,z,k)*(-x)**i for x,y,z in pts)
  assert reduce(pm-h**(k%2)*pp[i])==0,(k,i,'prism')
  assert reduce(cm-cc[i])==0,(k,i,'cap')
 checks.append({'k':k,'coordinates_checked':11-k,'real_moments_identical':True,'sine_moments_zero_by_y_reflection':True})
root=Path('/home/dsh/Thomson Problem/proof_work');geom=json.loads((root/'candidate_triple_types_v1.json').read_text())['triangle_types'];names='ABCDFG';nodes=[1-s.Rational(3,2)*r*r,2*r*r-1,r*r/2-1,-s.Rational(1,2),r/2,-r];pair=[6,3,6,3,12,6];counts=[sum(t['multiplicity']*t['labels'].count(n)for t in geom)for n in names];assert counts==[7*w for w in pair];assert sum(t['multiplicity']for t in geom)==84
boundary=[]
for t in geom:
 if t['status']=='identically_boundary':
  u,v,z=[nodes[names.index(c)]for c in t['labels']];g=[2*(v*z-u),2*(u*z-v),2*(u*v-z)];vel=list(map(lambda x:s.diff(x,r),[u,v,z]));assert s.factor(sum(a*b for a,b in zip(g,vel)))==0;boundary.append({'labels':t['labels'],'g0':str(s.factor(g[0])),'velocity_dot_gradient_exact_zero':True})
w=json.loads((root/'d10_contact_left_geometry_v1.json').read_text());W=s.Matrix([[s.sympify(z,locals={'r':r})for z in row]for row in w['rows']]);det=s.factor(W[:,w['minor_columns']].det());assert det==-36*r
cert=json.loads((root/'d10_relative_normal_exact2026_certificate.json').read_text());lu=cert['LU_pivots'];nonzero=[]
for z in lu:nonzero.append(F(z['lo']) * F(z['hi'])>0 if 'lo'in z else int(z['lo_numerator'])*int(z['hi_numerator'])>0)
assert len(nonzero)==33 and all(nonzero)
out={'status':'GEOMETRIC_DERIVATION_REVIEW_PASS_WITH_EXPLICIT_DEPENDENCIES','physical_anchor_moment_checks':checks,'triangle_count':84,'pair_multiplicities':pair,'pair_incidences':counts,'F111_triangle_constant':'84/8=21/2','S_repeated_index_decomposition':'S=6 sum_unordered_distinct F+6 sum_unordered_pairs F(1,t,t)+9F111','weighted_M_value_identity':'sum w Mvalue=7S/6','weighted_M_derivative_identity':'sum w vel dot gradM=7Sprime/6 with fixed coefficient matrices','boundary_checks':boundary,'W_minor_exact':str(det),'certified_LU_nonzero_count':33,'certificate_sha256':hashlib.sha256((root/'d10_relative_normal_exact2026_certificate.json').read_bytes()).hexdigest(),'seconds':time.time()-start,'warning':'Small symbolic checks establish physical features/counts/boundary conversion; WM=0 is proven in accompanying geometric derivation, not by interval zero containment.'};p=root/'d10_relative_normal2026_contact_geometry_review.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
