"""Connect saved full-root sphere proofs, cap capacity and exact six-point budget.
Uses archived global certificate as a dependency; does not replay its 202923 nodes.
"""
if not __debug__:raise RuntimeError('Assertions must be enabled')
from fractions import Fraction as F
from pathlib import Path
import hashlib,json,argparse
BASE=Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(replay=False):
 paths={key:BASE/name for key,name in {'model':'nonsharp_d10_root25_7599205_v10.json','global_certificate':'nonsharp_d10_root25_7599205_v10_result.json','chart_certificate':'fixed_triangle_two_caps_chart_certificate_v1.json','chart_verifier':'verify_fixed_triangle_two_caps_v1.py','budget':'fixed_triangle_two_cap_budget_exact_v1.json','pair_certificate':'pair056_optimized_certificate.json','bernstein':'exact_tensor_bernstein.py','interval':'certify_all_degree.py'}.items()}
 data={k:json.loads(p.read_text())for k,p in paths.items()if p.suffix=='.json'}
 model,glob,chart,budget=(data[k]for k in ['model','global_certificate','chart_certificate','budget'])
 assert glob['status']=='certified'and glob['pending']==0 and glob['model_sha256']==sha(paths['model'])
 assert chart['status']=='certified_fixed_triangle_two_cap_bounds'and chart['root_only']
 for k,name in [('source_sha256','model'),('verifier_sha256','chart_verifier'),('bernstein_dependency_sha256','bernstein'),('interval_dependency_sha256','interval')]:assert chart[k]==sha(paths[name])
 assert budget['model_sha256']==sha(paths['model'])
 u,v,t=map(F,chart['anchor_parameter']);assert [u,v,t]==list(map(F,budget['point']))
 r=sum(F(z)*u**e[0]*v**e[1]*t**e[2]for e,z in model['residual_monomial'])
 upper=F(budget['U']);lower=F(model['target']);assert lower==F(glob['target'])==F(budget['B']);assert upper==F(data['pair_certificate']['U'])
 K=7*(upper-lower)-r
 assert r==F(budget['R_fixed_triangle'])and K==F(budget['six_point_phi_budget'])
 h=F(chart['cap_height']);pair=F(chart['pair_inner_product_upper']);assert pair==F(14,25)
 for row in chart['cap_centers']:assert sum(F(x)**2 for x in row)<=1
 assert 2*h*h-1>pair
 m,tau=F(chart['global_phi_lower']),F(chart['outside_caps_phi_lower']);assert 0<=m<=tau
 sixlower=2*m+4*tau;assert sixlower>K
 for result in chart['results']:
  assert result['pending']==0
  leaves=result['terminal_leaves'];assert len(leaves)==result['positive_leaves']+result['excluded_leaves']
  area=F(0);rects=[]
  for leaf in leaves:
   x,dx,y,dy=leaf['box_dyadic'];assert 0<=x<2**dx and 0<=y<2**dy
   rect=(F(x,2**dx),F(x+1,2**dx),F(y,2**dy),F(y+1,2**dy));rects.append(rect);area+=F(1,2**(dx+dy))
   mins=leaf['lower_coefficients']
   if leaf['type']=='anchor_excluded':assert max(mins[2:5])>0
   elif leaf['type']=='positive_inside_cap':assert mins[0]>=0 and max(mins[5:])>0
   else:assert leaf['type']=='positive_tau'and mins[0]>=0 and mins[1]>=0
  assert area==1
  for i,a in enumerate(rects):
   for b in rects[:i]:assert max(a[0],b[0])>=min(a[1],b[1])or max(a[2],b[2])>=min(a[3],b[3])
 assert {z['chart']for z in chart['results']}=={-1,1}
 if replay:
  import verify_fixed_triangle_two_caps_v1 as verifier
  fresh=verifier.run();assert fresh['status']==chart['status']
  assert [z['tree_sha256']for z in fresh['results']]==[z['tree_sha256']for z in chart['results']]
 result={'status':'fixed_triangle_six_external_points_excluded','scope':'Fixed rational triangle only. Global root certificate is a hashed dependency; no new unconditional energy lower bound.','triangle':[str(x)for x in [u,v,t]],'six_point_phi_lower':str(sixlower),'six_point_phi_budget':str(K),'strict_margin':str(sixlower-K),'display_only':{'lower':float(sixlower),'budget':float(K),'margin':float(sixlower-K)},'sphere_charts_complete':True,'leaf_partition_independent_audit':True,'chart_replayed_this_run':replay,'dependencies':{k:{'path':str(p),'sha256':sha(p)}for k,p in paths.items()},'verifier_sha256':sha(Path(__file__))}
 return result
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--replay',action='store_true');args=parser.parse_args();result=run(args.replay)
 out=BASE/'sixq_cover2026_fixed_triangle_exclusion.json';out.write_text(json.dumps(result,indent=2)+'\n');print(result['status'],result['display_only']);print('Saved',out)
