"""Recompute union of unary bounds and exact capacity exclusions; no unresolved pair omitted."""
if not __debug__:raise RuntimeError('Assertions required')
from pathlib import Path
from fractions import Fraction as F
import json,hashlib
BASE=Path(__file__).parent
def run():
 cpath=BASE/'t2_low_cells2026_capacity.json';ppath=BASE/'t2_unary_leaf_pair2026_result.json';saved=BASE/'t2_low_pair2026_combined_pruning.json'
 cap=json.loads(cpath.read_text());pair=json.loads(ppath.read_text());out=json.loads(saved.read_text())
 for path in [cpath,ppath]:assert out['dependencies'][path.name]==hashlib.sha256(path.read_bytes()).hexdigest()
 a,b=cap['cells'],pair['cell_bounds'];assert len(a)==len(b)==894
 for x,y in zip(a,b):assert (x['sign'],x['location'])==(y['sign'],y['location'])
 gid={};same=0
 for g,row in enumerate(cap['groups']):
  assert row['capacity_one'];bounds=[list(map(F,z))for z in row['coordinate_bounds']]
  d2=sum((hi-lo)**2 for lo,hi in bounds);assert d2==F(row['diameter_squared_upper'])<F(22,25)
  for i in row['cell_indices']:assert i not in gid;gid[i]=g
  same+=len(row['cell_indices'])**2
 assert sorted(gid)==list(range(len(a)))
 lower=[F(x['phi_lower'])for x in b];accepted=overlap=remaining=0
 for i in range(len(a)):
  for j in range(len(a)):
   high=lower[i]+lower[j]>=F(1,5000);near=gid[i]==gid[j]
   accepted+=high;overlap+=high and near;remaining+=not(high or near)
 assert accepted==out['phi_pair_accepted']==303673 and same==out['same_capacity_group_infeasible']==56084
 assert overlap==out['overlap']==19105 and remaining==out['remaining_ordered_pairs']==458584
 assert accepted+same-overlap==out['union_accepted_or_excluded']==340652
 assert remaining%2==0
 print('VERIFIED_PARTIAL_UNION',accepted+same-overlap,'remaining_unordered',remaining//2)
 return {'verified_partial_union':True,'remaining_unordered':remaining//2,'scope':'Given the saved unary and geometric-capacity certificates; no full pair proof.'}
if __name__=='__main__':run()
