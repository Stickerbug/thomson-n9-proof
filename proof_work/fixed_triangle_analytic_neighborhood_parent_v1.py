"""Exact rational neighborhood exclusion; archived root certificates are dependencies.
No resumption of a pending frontier, no new unconditional energy lower bound.
"""
if not __debug__:raise RuntimeError('Assertions must be enabled')
from fractions import Fraction as F
from pathlib import Path
import json,hashlib
BASE=Path(__file__).parent
load=lambda name:json.loads((BASE/name).read_text())
sha=lambda name:hashlib.sha256((BASE/name).read_bytes()).hexdigest()
modelname='nonsharp_d10_root25_7599205_v10.json'
model=load(modelname);chart=load('fixed_triangle_two_caps_widened_certificate_v1.json');budget=load('fixed_triangle_two_cap_budget_exact_v1.json');root=load('nonsharp_d10_root25_7599205_v10_result.json')
assert root['status']=='certified' and root['pending']==0 and root['model_sha256']==sha(modelname)
assert chart['status']=='certified_fixed_triangle_two_cap_bounds' and chart['root_only'] and chart['source_sha256']==sha(modelname)
assert {x['chart']for x in chart['results']}=={-1,1} and all(x['pending']==0 for x in chart['results'])
u,v,t=map(F,chart['anchor_parameter']);assert [u,v,t]==list(map(F,budget['point']))
assert budget['model_sha256']==sha(modelname)
U=F(budget['U']);B=F(model['target']);assert B==F(root['target'])==F(budget['B'])
assert U==F(load('pair056_optimized_certificate.json')['U'])
terms=[(tuple(e),F(c))for e,c in model['residual_monomial']]
Rc=sum(c*u**e[0]*v**e[1]*t**e[2]for e,c in terms)
K=7*(U-B)-Rc;assert K==F(budget['six_point_phi_budget'])
S=sum(abs(c)*sum(e)for e,c in terms)
assert S==F(chart['derivative_coefficient_sum'])
delta=F(1,10**13)
# These rational bounds hold on every line segment in the whole parameter cube.
uabs=F(19,25);vabs=F(3,10);smin=F(16,25);nabs=F(13,100);czmin=F(9,10)
assert abs(u)+delta<uabs and abs(v)+delta<vabs
assert abs(t-u*v)+delta*(1+abs(u)+abs(v))+delta**2<nabs
assert 1-uabs*uabs>smin*smin
wabs=nabs/smin;assert 1-vabs*vabs-wabs*wabs>czmin*czmin
# b=(u,sqrt(1-u²),0), w=(t-uv)/sqrt(1-u²), c=(v,w,sqrt(1-v²-w²)).
Lb=1+uabs/smin;Lw=vabs/smin+nabs*uabs/smin**3+uabs/smin+1/smin
Lc=1+Lw+(vabs+wabs*Lw)/czmin
assert Lb<3 and Lc<8
pair=F(chart['pair_inner_product_upper']);assert pair==F(14,25)
assert pair+8*delta<F(chart['allowed_anchor_dot_upper'])
# Fixed-center widened sphere proof applies to the SAME six external points.
# Their anchor dots move by <=8delta; phi moves by <=24 S delta each.
h=F(chart['cap_height']);assert 2*h*h-1>pair
assert all(sum(F(x)**2 for x in row)<=1 for row in chart['cap_centers'])
m=F(chart['global_phi_lower']);M=F(chart['outside_caps_phi_lower']);assert 0<=m<=M
centerlower=2*m+4*M
newlower=centerlower-144*S*delta;newbudget=K+S*delta
margin=newlower-newbudget;assert margin>0
names=[modelname,'nonsharp_d10_root25_7599205_v10_result.json','pair056_optimized_certificate.json','fixed_triangle_two_caps_widened_certificate_v1.json','fixed_triangle_two_cap_budget_exact_v1.json','verify_fixed_triangle_two_caps_widened_v1.py']
result={'status':'certified_parameter_neighborhood_exclusion_conditional_on_archived_root_proofs','scope':'Every competitive nine-point configuration E<=U has no unordered triangle whose ordered inner products lie in this box. In fact all box triangles are excluded. Not a global sharp proof.','center':list(map(str,[u,v,t])),'parameter_supnorm_radius':str(delta),'derivative_coefficient_sum':str(S),'anchor_b_L1_derivative_bound':str(Lb),'anchor_c_L1_derivative_bound':str(Lc),'six_external_cost_lower':str(newlower),'six_external_budget_upper':str(newbudget),'strict_margin':str(margin),'display_only':{'radius':float(delta),'S':float(S),'margin':float(margin)},'proof':'On the whole cube s>=16/25, |w|<=13/64, c_z>=9/10. Integrating L1 derivative bounds gives anchor displacements <=3delta and <=8delta. Each polynomial R moves by at most S times its input supnorm change. Hence six phi terms lose at most144 S delta and budget increases by at most S delta. Fixed caps retain capacity one under pair dot<14/25. The widened fixed-center chart proof gives two m plus four M. Positive remaining margin excludes the whole cube.','archived_dependencies':{n:sha(n)for n in names},'verifier_sha256':sha(Path(__file__).name)}
output=BASE/'fixed_triangle_analytic_neighborhood_parent_v1.json';output.write_text(json.dumps(result,indent=2)+'\n');print(result['status']);print(result['display_only'])
