"""Finite native/stepwise object arithmetic and conditional-coverage smoke."""
from fractions import Fraction as F
from pathlib import Path
import json,random,time
import numpy as np
from exact128_2026 import NativeTensor,LIMIT
from sharp_global_native128_2026_engine import check_away,GRAM
from sharp_global_away2026_engine import check_away as old_check
start=time.monotonic();rng=random.Random(20260624);checks=[]
def step_object(t,axis,upper):
 a=np.moveaxis(t,axis,0);row=a.copy();left=np.empty_like(a);right=np.empty_like(a);left[0],right[0]=row[0],row[-1]
 for j in range(1,len(a)):
  row=(row[:-1]+row[1:]+int(upper))//2;left[j],right[j]=row[0],row[-1]
 return np.moveaxis(left,0,axis),np.moveaxis(right[::-1],0,axis)
for upper in [False,True]:
 for trial in range(40):
  shape=(rng.randrange(1,7),rng.randrange(1,5),rng.randrange(1,4));t=np.array([rng.randrange(-(1<<110),1<<110)for _ in range(int(np.prod(shape)))],dtype=object).reshape(shape)
  if trial==0:t.flat[0]=-LIMIT+1;t.flat[-1]=LIMIT-1
  native=NativeTensor(t);assert native.min()==int(t.min()) and native.max()==int(t.max());got=native.split(trial%3,upper);truth=step_object(t,trial%3,upper)
  for side in [0,1]:assert np.array_equal(got[side].to_object(),truth[side])
checks.append('80 random signed128 upper/lower splits equal independent Python-object STEPWISE floor/ceil, including strict +/-2^124 extrema')
for value in [-LIMIT,LIMIT]:
 try:NativeTensor(np.array([[[value]]],dtype=object))
 except OverflowError:pass
 else:raise AssertionError('unsafe native cast accepted')
checks.append('unsafe strict endpoints refused before native arithmetic')
def ints(p):return {k:(v,v)for k,v in p.items()}
q={(2,0,0):F(1),(0,2,0):F(1),(0,0,2):F(1)};positive=q|{(0,0,0):F(1,1000)}
a=check_away(ints(positive),[],[],10000,5);b=old_check(ints(positive),[],[],10000,5)
assert a['status']==b['status']=='away_certified_given_local_regions' and a['pending_count']==b['pending_count']==0
checks.append('Native and old final-binomial-outward backends independently close same positive quadratic full-root tree; no integer-equality assumption')
center=[(F(-23,100),F(-21,100))]*3
local=check_away(ints(q),[{'center':center,'halfwidth':F(79,100),'id':'whole-root'}],[],1,5);assert local['counts']['local_region']==1 and local['pending_count']==0
reject=check_away(ints(q),[{'center':center,'halfwidth':F(78,100),'id':'reject-midpoint'}],[],1,5);assert reject['counts']['local_region']==0 and reject['pending_count']==2
comp=check_away(ints(GRAM),[],[{'centerI':[(F(0),F(0))]*3,'lambda':F(1),'activation_radius':F(3),'id':'S-zero'}],1,5);assert comp['counts']['boundary_multiplier']==1 and comp['pending_count']==0
pending=check_away({(0,0,0):(F(-1),F(-1))},[],[],0,5);assert pending['pending_count']==1
for r in [a,local,reject,comp,pending]:
 assert all(r['root_coverage'].values()) and r['restart_from_full_root'] and not r['frontier_resumed']
checks.append('local and S=R-g terminal toys ACTUALLY TRIGGER; uncertain-center midpoint shortcut rejected; complete pending and coverage identities')
report={'status':'SMOKE_PASSED','conditional_only':True,'seconds':time.monotonic()-start,'checks':checks,'native_positive':{k:a[k]for k in ['visited_nodes','counts','pending_count','native_tensor_split_calls','native_backend_sha256']},'local_counts':local['counts'],'S_counts':comp['counts']}
out=Path(__file__).with_suffix('.json');assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
