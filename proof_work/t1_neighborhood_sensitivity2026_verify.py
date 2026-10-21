"""Exact analytic extension of a certified fixed-triangle sphere certificate.
No root positivity or sphere charts are recomputed. Assertions must be enabled.
"""
if not __debug__:raise RuntimeError('Assertions must be enabled')
from pathlib import Path
from fractions import Fraction as F
import json,hashlib
BASE=Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run():
 names={'model':'nonsharp_d10_root25_7599205_v10.json','global_certificate':'nonsharp_d10_root25_7599205_v10_result.json','chart':'fixed_triangle_two_caps_widened_certificate_v1.json','chart_verifier':'verify_fixed_triangle_two_caps_widened_v1.py','budget':'fixed_triangle_two_cap_budget_exact_v1.json','bernstein':'exact_tensor_bernstein.py','interval':'certify_all_degree.py'}
 paths={k:BASE/v for k,v in names.items()};data={k:json.loads(p.read_text())for k,p in paths.items()if p.suffix=='.json'}
 model,glob,chart,budget=(data[k]for k in ['model','global_certificate','chart','budget'])
 assert glob['status']=='certified'and glob['pending']==0 and glob['model_sha256']==sha(paths['model'])
 assert chart['status']=='certified_fixed_triangle_two_cap_bounds'and chart['root_only']
 assert {r['chart']for r in chart['results']}=={-1,1}and all(r['pending']==0 for r in chart['results'])
 for k,name in [('source_sha256','model'),('verifier_sha256','chart_verifier'),('bernstein_dependency_sha256','bernstein'),('interval_dependency_sha256','interval')]:assert chart[k]==sha(paths[name])
 assert budget['model_sha256']==sha(paths['model'])
 T=list(map(F,chart['anchor_parameter']));assert T==list(map(F,budget['point']))
 terms=[(tuple(e),F(c))for e,c in model['residual_monomial']]
 Sall=sum(abs(c)*sum(e)for e,c in terms);Slast2=sum(abs(c)*(e[1]+e[2])for e,c in terms)
 assert Slast2==F(chart['derivative_coefficient_sum'])and Sall>Slast2
 delta=F(1,10**13);cube=[(x-delta,x+delta)for x in T]
 absu=max(map(abs,cube[0]));absv=max(map(abs,cube[1]));uv=[x*y for x in cube[0]for y in cube[1]];tw=(cube[2][0]-max(uv),cube[2][1]-min(uv));absnum=max(map(abs,tw))
 assert absu<F(76,100)and absv<F(3,10)and absnum<F(13,100)
 s0=F(64,100);wmax=F(13,100)/s0;cz0=F(9,10)
 assert 1-F(76,100)**2>s0*s0
 assert 1-F(3,10)**2-wmax*wmax>cz0*cz0
 Lb=1+F(76,100)/s0
 Lw=F(3,10)/s0+F(13,100)*F(76,100)/s0**3+F(76,100)/s0+1/s0
 Lc=1+Lw+(F(3,10)+wmax*Lw)/cz0
 assert Lb<3 and Lc<8
 assert F(14,25)+8*delta<F(chart['allowed_anchor_dot_upper'])
 # On the entire cube s>=s0 and cz>=cz0, so the Cholesky map is smooth.
 # All old and new R arguments and straight interpolation remain in [-1,1].
 # Thus |Delta R|<=Sall*maxnorm(Delta inputs), using the coefficient l1 derivative bound.
 phi_error=24*Sall*delta;six_error=6*phi_error;budget_error=Sall*delta
 h=F(chart['cap_height']);assert 2*h*h-1>F(14,25)
 for center,norm in zip(chart['cap_centers'],chart['cap_norm_squared']):
  assert sum(F(z)**2 for z in center)==F(norm)<=1
 m,tau=F(chart['global_phi_lower']),F(chart['outside_caps_phi_lower']);assert m<=tau
 sixfixed=2*m+4*tau;assert sixfixed==F(chart['six_point_cost_lower'])
 R0=sum(c*T[0]**e[0]*T[1]**e[1]*T[2]**e[2]for e,c in terms)
 U,B=F(budget['U']),F(model['target']);assert B==F(glob['target'])==F(budget['B'])
 K=7*(U-B)-R0;assert R0==F(budget['R_fixed_triangle'])and K==F(budget['six_point_phi_budget'])
 lower=sixfixed-six_error;upper=K+budget_error;margin=lower-upper
 assert margin>0
 output={'status':'certified_fixed_triangle_parameter_cube_excluded_conditional_on_hashed_certificates','scope':'Every triangle in the closed coordinate cube of radius 1e-13 around T is excluded from competitive nine-point configurations subject to the existing pair-dot bound and archived global energy decomposition. No global root or chart replay is performed.','T':list(map(str,T)),'delta':str(delta),'cube':[[str(a),str(b)]for a,b in cube],'S_all_axes':str(Sall),'S_last_two_axes':str(Slast2),'bounds':{k:str(v)for k,v in {'abs_u':absu,'abs_v':absv,'abs_t_minus_uv':absnum,'s_lower':s0,'w_abs_upper':wmax,'cz_lower':cz0,'b_gradient_l1_upper':Lb,'w_gradient_l1_upper':Lw,'c_gradient_l1_upper':Lc,'anchor_max_displacement':8*delta,'phi_error':phi_error,'six_phi_error':six_error,'budget_error':budget_error,'six_phi_lower':lower,'budget_upper':upper,'strict_margin':margin}.items()},'display_only':{'S_all_axes':float(Sall),'six_phi_lower':float(lower),'budget_upper':float(upper),'margin':float(margin)},'dependencies':{k:{'path':str(p),'sha256':sha(p)}for k,p in paths.items()},'verifier_sha256':sha(Path(__file__))}
 return output
if __name__=='__main__':
 result=run();out=BASE/'t1_neighborhood_sensitivity2026_certificate.json';out.write_text(json.dumps(result,indent=2)+'\n');print(result['status']);print(result['display_only']);print('SAVED',out)
