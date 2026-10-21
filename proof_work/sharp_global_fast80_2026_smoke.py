"""Finite independent exact tests for hybrid arithmetic and physical-node coverage."""
from fractions import Fraction as F
from pathlib import Path
import json,random
import numpy as np
from exact_tensor_bernstein import coefficients
from sharp_global_fast80_2026_engine import check_away,split_int64,coarsen80,RootReplay80,ROOT_BOX,GRAM,SAFE_ABS,FINE_SAFE_ABS,try_cast80

def fraction_split(t,axis):
 a=np.moveaxis(np.array([F(int(z))for z in t.flat],dtype=object).reshape(t.shape),axis,0);n=len(a)-1;row=a.copy();left=np.empty_like(a);right=np.empty_like(a);left[0],right[0]=row[0],row[-1]
 for j in range(1,n+1):row=(row[:-1]+row[1:])/2;left[j],right[j]=row[0],row[-1]
 return np.moveaxis(left,0,axis),np.moveaxis(right[::-1],0,axis)
checks=[];rng=random.Random(20260623)
for upper in [False,True]:
 for trial in range(100):
  shape=(rng.randrange(1,7),rng.randrange(1,5),rng.randrange(1,4));values=[rng.randrange(-FINE_SAFE_ABS+1,FINE_SAFE_ABS)for _ in range(int(np.prod(shape)))];t=np.array(values,dtype=np.int64).reshape(shape);axis=trial%3;got=split_int64(t,axis,upper);truth=fraction_split(t,axis)
  for side in [0,1]:assert all(F(int(x))>=y if upper else F(int(x))<=y for x,y in zip(got[side].flat,truth[side].flat))
checks.append('100 random lower + 100 random upper int64 splits enclose independent Fraction de Casteljau, including near-2^62 signed values')
try:coarsen80(np.array([1<<93],dtype=object))
except AssertionError:checks.append('unsafe coarse cast rejected before int64 conversion')
else:raise AssertionError('unsafe cast accepted')
edge=np.array([-FINE_SAFE_ABS+1,FINE_SAFE_ABS-1,-FINE_SAFE_ABS+1,FINE_SAFE_ABS-1,-1,0,1],dtype=np.int64)
for upper in [False,True]:
 for values in [edge,np.full(7,FINE_SAFE_ABS-1,dtype=np.int64),np.full(7,-FINE_SAFE_ABS+1,dtype=np.int64)]:
  got=split_int64(values,0,upper);truth=fraction_split(values,0)
  for side in [0,1]:assert all(F(int(x))>=y if upper else F(int(x))<=y for x,y in zip(got[side].flat,truth[side].flat))
checks.append('strict +/-2^62 edge extrema and alternating endpoints: upper/lower all Fraction-enclose without overflow')
raw=edge.astype(object);fast,cast=try_cast80(raw);assert cast and fast.dtype==np.int64 and np.array_equal(fast.astype(object),raw);assert all(F(int(x),1<<80)==F(int(y),1<<80)for x,y in zip(raw,fast));assert raw.dtype==object
for endpoint in [-FINE_SAFE_ABS,FINE_SAFE_ABS,-(1<<100),1<<100]:
 unsafe=np.array([endpoint],dtype=object);kept,cast=try_cast80(unsafe);assert not cast and kept is unsafe and kept.dtype==object
checks.append('80-bit scale and EACH integer preserved exactly by safe cast; strict endpoints/huge unsafe inputs refused; original object unchanged')
p={(i,j,k):F(rng.randrange(-10,11),rng.randrange(1,17))for i in range(4)for j in range(3)for k in range(3)};b=coefficients(p,ROOT_BOX,bits=80);g=coefficients(GRAM,ROOT_BOX,bits=80,upper=True);replay=RootReplay80(b,g,{},[],maxsize=64)
for trial in range(12):
 path=('001101'*8)[:trial+5]+str(trial%2);rb,rg,rs,box,levels=replay(path);directb=coefficients(p,box,bits=80);directg=coefficients(GRAM,box,bits=80,upper=True);assert np.all(rb<=directb)and np.all(rg>=directg);assert len(path)==sum(levels);assert len(replay.cache)<=64
assert replay.root[0].dtype==object and all(state[0].dtype==object for state in replay.cache.values());checks.append('12 cached full-binary-path original-root80 replays outward-enclose independent exact transforms on SAME physical box')
def ints(p):return {k:(v,v)for k,v in p.items()}
positive=check_away({(0,0,0):(F(1),F(3))},[],[],10,5);assert positive['counts']['positive']==1 and positive['pending_count']==0
zero=check_away({(0,0,0):(F(-1),F(-1))},[],[],0,5);assert zero['pending_count']==1 and zero['pending'][0]['precision_bits']==48
q={(2,0,0):F(1),(0,2,0):F(1),(0,0,2):F(1)};center=[(F(-23,100),F(-21,100))]*3
local=check_away(ints(q),[{'center':center,'halfwidth':F(79,100),'id':'whole-root'}],[],1,5);assert local['counts']['local_region']==1
small=check_away(ints(q),[{'center':center,'halfwidth':F(78,100),'id':'reject-midpoint'}],[],1,5);assert small['counts']['local_region']==0 and small['pending_count']==2
comp=check_away(ints(GRAM),[],[{'centerI':[(F(0),F(0))]*3,'lambda':F(1),'activation_radius':F(3),'id':'S-zero'}],1,5);assert comp['counts']['boundary_multiplier']==1 and comp['pending_count']==0
checks.append('tiny positive, budget-zero pending, uncertain-center local containment, S=R-g, coverage identities')
q[(0,0,0)]=F(1,10**20);up=check_away(ints(q),[],[],20000,10);assert up['precision_upgrades']>0 and up['pending_count']==0 and up['status']=='away_certified_given_local_regions';assert up['dtype_cast_counts']['B']>0 and up['fine_tensor_splits_by_role']['B']['int64']>0;checks.append('known positive quadratic+1e-20 TRIGGERS original-root80 upgrade, same-scale int64 fine splits, and closes full tree')
report={'status':'SMOKE_PASSED','checks':checks,'upgrade_example':{k:up[k]for k in ['visited_nodes','split_nodes','pending_count','precision_upgrades','coarse_visited','fine_visited','terminal_precision_counts','root80_replay_split_steps','root_coverage','dtype_cast_counts','fine_tensor_splits','fine_tensor_splits_by_role','fine_work_scale_unchanged']},'replay_test_cache_hits':replay.cache_hits,'conditional_only':True};out=Path(__file__).with_name('sharp_global_fast80_2026_smoke.json');assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
