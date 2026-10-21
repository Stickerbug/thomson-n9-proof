"""Exact narrow-edge Bernstein derivative slabs; no Gram pruning."""
if not __debug__:raise RuntimeError('Assertions must be enabled')
from pathlib import Path
from fractions import Fraction as F
import json,time,hashlib
from exact_tensor_bernstein import coefficients
BASE=Path(__file__).parent
BITS=64;SCALE=1<<BITS
def run():
 start=time.monotonic()
 import t1_neighborhood_sensitivity2026_verify as old
 base=old.run();chart=json.loads((BASE/'fixed_triangle_two_caps_widened_certificate_v1.json').read_text());budget=json.loads((BASE/'fixed_triangle_two_cap_budget_exact_v1.json').read_text());model=json.loads((BASE/'nonsharp_d10_root25_7599205_v10.json').read_text());v2path=BASE/'t1_neighborhood_sensitivity2026_neighbor_v2_certificate.json';v2=json.loads(v2path.read_text())
 poly={tuple(e):F(c)for e,c in model['residual_monomial']};T=list(map(F,chart['anchor_parameter']));rho=F(1,10**9);cap=F(chart['allowed_anchor_dot_upper']);slabs=[]
 for i,edge in enumerate(T):
  box=[(edge-rho,edge+rho),(F(-1),cap),(F(-1),cap)];bounds=[]
  for axis in range(3):
   deriv={tuple(e[j]-(j==axis)for j in range(3)):c*e[axis]for e,c in poly.items()if e[axis]}
   lo=coefficients(deriv,box,bits=BITS);hi=coefficients(deriv,box,bits=BITS,upper=True);lower=F(int(lo.min()),SCALE);upper=F(int(hi.max()),SCALE);bound=max(abs(lower),abs(upper));bounds.append(bound)
   print('SLAB',i,'AXIS',axis,'bound',float(bound),'seconds',time.monotonic()-start,flush=True)
  slabs.append({'edge':str(edge),'box':[[str(a),str(b)]for a,b in box],'axis_maxabs':list(map(str,bounds)),'phi_component_L':str(bounds[0]+8*bounds[1]+8*bounds[2])})
 L=sum(F(row['phi_component_L'])for row in slabs);Sbudget=F(v2['Lipschitz_S']);K=F(budget['six_point_phi_budget']);six=F(chart['six_point_cost_lower']);trials=[]
 for delta in [F(1,10**9),F(1,10**10),F(1,10**11)]:
  cube=[(x-delta,x+delta)for x in T];uv=[a*b for a in cube[0]for b in cube[1]];num=(cube[2][0]-max(uv),cube[2][1]-min(uv));coarse=max(map(abs,cube[0]))<F('.76')and max(map(abs,cube[1]))<F('.3')and max(map(abs,num))<F('.13');slack=F('.56')+8*delta<cap;lower=six-6*L*delta;upper=K+Sbudget*delta;margin=lower-upper
  trials.append({'delta':str(delta),'coarse_bounds_pass':coarse,'anchor_slack_pass':slack,'six_phi_lower':str(lower),'budget_upper':str(upper),'margin':str(margin),'pass':coarse and slack and delta<=rho and margin>0})
 chosen=next((r for r in trials if r['pass']),None)
 report={'status':'certified_fixed_triangle_neighborhood_v3_conditional_on_hashed_dependencies'if chosen else 'slab_derivative_attempt_no_improvement','warning':'Full rational slabs only; no Gram pruning; budget derivative bound reused from verified v2 certificate.','slab_radius':str(rho),'slabs':slabs,'phi_L':str(L),'budget_S':str(Sbudget),'trials':trials,'chosen':chosen,'dependencies':base['dependencies'],'v1_verifier_sha256':hashlib.sha256((BASE/'t1_neighborhood_sensitivity2026_verify.py').read_bytes()).hexdigest(),'v2_certificate_sha256':hashlib.sha256(v2path.read_bytes()).hexdigest(),'v3_verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'seconds':time.monotonic()-start,'display_only':{'phi_L':float(L),'budget_S':float(Sbudget),'chosen_delta':float(F(chosen['delta']))if chosen else None,'margin':float(F(chosen['margin']))if chosen else None}}
 return report
if __name__=='__main__':
 report=run();out=BASE/'t1_neighborhood_sensitivity2026_neighbor_v3_certificate.json';out.write_text(json.dumps(report,indent=2)+'\n');print(report['display_only']);print('SAVED',out)
