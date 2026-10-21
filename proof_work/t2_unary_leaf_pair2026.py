"""Exact recovery of phi lower bounds from archived low unary leaves.
Conditional on the archived root Bernstein construction and geometric R>=0.
Does not evaluate or certify any remaining low pair.
"""
if not __debug__:raise RuntimeError('Assertions required')
from pathlib import Path
from fractions import Fraction as F
import json,bisect,hashlib
BASE=Path(__file__).parent
def run():
 src=BASE/'t2_unary_screen2026_result.json';r=json.loads(src.read_text());lower=[];records=[]
 assert r['status']=='partial_unary_screen_not_pair_certificate' and r['threshold']=='1/5000'
 assert len(r['results'])==2 and {c['sign']for c in r['results']}=={-1,1}
 assert all(c['counts'].get('budget_pending',0)==0 for c in r['results']), 'Unvisited unary boxes must remain unresolved; no pair pruning allowed'
 assert all(l['kind'] in {'low_pending','phi_high','excluded_anchor_or_disk'} for c in r['results'] for l in c['leaves'])
 for chart in r['results']:
  for leaf in chart['leaves']:
   if leaf['kind']!='low_pending':continue
   x,dx,y,dy=leaf['location'];bounds=[(F(2*x,1<<dx)-1,F(2*(x+1),1<<dx)-1),(F(2*y,1<<dy)-1,F(2*(y+1),1<<dy)-1)]
   def minsq(a,b):return F(0)if a<=0<=b else min(a*a,b*b)
   d=1+sum(minsq(a,b)for a,b in bounds);b=leaf['lower_coefficients'][0];assert b<0
   lb=max(F(0),F(r['threshold'])+F(b,1<<r['bits'])/d**27);lower.append(lb)
   records.append({'sign':chart['sign'],'location':leaf['location'],'D_lower':str(d),'phi_lower':str(lb)})
 vals=sorted(lower);threshold=F(1,5000)
 accepted=sum(len(vals)-bisect.bisect_left(vals,threshold-a)for a in vals)
 out={'status':'partial_pair_acceptance_conditional_on_unary_certificate','cells':len(vals),'ordered_low_pairs':len(vals)**2,'accepted_via_two_phi_bounds':accepted,'remaining_ordered_pairs':len(vals)**2-accepted,'threshold_W':'1/25000','phi_sum_threshold':str(threshold),'zero_unary_bounds':sum(a==0 for a in vals),'formula':'phi >= TAU + b_min/(2^bits D_min^27), since b_min<0; EPS in polynomial threshold dominates anchor approximation error. Clip to zero using old geometric nonnegativity.','pair_implication':'If phi_lower(q_cell)+phi_lower(r_cell)>=1/5000 then W>=1/25000 on the feasible pair subset, using psi>=0.','warning':'No claim for remaining pairs; root polynomial construction and old global R proof are dependencies, not recomputed here.','source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'cell_bounds':records}
 (BASE/'t2_unary_leaf_pair2026_result.json').write_text(json.dumps(out,indent=2)+'\n')
 print({k:out[k]for k in ['status','cells','ordered_low_pairs','accepted_via_two_phi_bounds','remaining_ordered_pairs','zero_unary_bounds']})
 return out
if __name__=='__main__':run()
