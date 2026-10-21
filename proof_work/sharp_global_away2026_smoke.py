"""Small exact-arithmetic and conditional-coverage smoke checks; no real kernel scan."""
from fractions import Fraction as F
from pathlib import Path
import json,random
import numpy as np
from sharp_global_away2026_engine import check_away,split_outward,ROOT_BOX,GRAM
from exact_tensor_bernstein import coefficients

def intervals(p):return {k:(v,v)for k,v in p.items()}
rows=[]
for seed in range(12):
 rng=random.Random(seed);p={(i,j,k):F(rng.randrange(-15,16),rng.randrange(1,15))for i in range(4)for j in range(3)for k in range(2)}
 for upper in [False,True]:
  root=coefficients(p,ROOT_BOX,bits=23,upper=upper);axis=seed%3;children=split_outward(root,axis,upper)
  lo,hi=ROOT_BOX[axis];mid=(lo+hi)/2
  for side in [0,1]:
   box=list(ROOT_BOX);box[axis]=(lo,mid)if side==0 else(mid,hi);direct=coefficients(p,box,bits=23,upper=upper)
   assert np.all(children[side]>=direct)if upper else np.all(children[side]<=direct)
rows.append('48 independently transformed child tensors outward-enclosed')
pos=check_away({(0,0,0):(F(1),F(3))},[],[],10,5);assert pos['counts']['positive']==1 and pos['eps']=='1' and not pos['pending'];rows.append('constant interval positive')
pending=check_away({(0,0,0):(F(-1),F(-1))},[],[],0,5);assert pending['pending_count']==1 and pending['pending'][0]['path']=='';rows.append('budget zero retains whole root')
negative=check_away({(0,0,0):(F(-1),F(-1))},[],[],100,5);assert negative['counts']['gram_negative']>0 and negative['pending_count']>0;rows.append('Gram-negative pruning with complete pending')
q={(2,0,0):F(1),(0,2,0):F(1),(0,0,2):F(1)};center=[(F(-23,100),F(-21,100))]*3
full=check_away(intervals(q),[{'center':center,'halfwidth':F(79,100),'id':'uncertain-root-cover'}],[],1,5);assert full['counts']['local_region']==1;rows.append('uncertain center intersection contains full root')
small=check_away(intervals(q),[{'center':center,'halfwidth':F(78,100),'id':'midpoint-would-be-unsound'}],[],1,5);assert small['counts']['local_region']==0 and small['pending_count']==2;rows.append('midpoint-only containment correctly rejected')
boundary=check_away(intervals(GRAM),[],[{'centerI':[(F(0),F(0))]*3,'lambda':F(1),'activation_radius':F(3),'id':'g-itself'}],1,5);assert boundary['counts']['boundary_multiplier']==1 and not boundary['pending'];rows.append('R=g compensated S=R-g=0 closes root on Gram')
for invalid in [('float',lambda:check_away({(0,0,0):(1.0,1.0)},[],[],1,1)),('negative-lambda',lambda:check_away(intervals(q),[],[{'centerI':[(0,0)]*3,'lambda':F(-1)}],1,1))]:
 try:invalid[1]()
 except (TypeError,AssertionError):rows.append(invalid[0]+' rejected')
 else:raise AssertionError(invalid[0])
result={'status':'SMOKE_PASSED','checks':rows,'conditional_only':True};out=Path(__file__).with_name('sharp_global_away2026_smoke.json');assert not out.exists();out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
