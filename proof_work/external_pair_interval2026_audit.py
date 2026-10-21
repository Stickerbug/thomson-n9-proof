#!/usr/bin/env python3
"""Read-only independent tree/coverage and cap-rejection audit. Not a W proof."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import json,hashlib
from dyadic_interval import I,S,BITS,ceildiv
if not __debug__:raise RuntimeError('Assertions must remain enabled; do not use -O')
BASE=Path(__file__).resolve().parent
P='external_pair_interval2026_'
def square(a):
 lo=0 if a.lo<=0<=a.hi else min(a.lo*a.lo,a.hi*a.hi)
 return I(lo//S,ceildiv(max(a.lo*a.lo,a.hi*a.hi),S),raw=True)
def chart(bb,sign):
 x,y=[I(*pair,raw=True)for pair in bb];xx,yy=square(x),square(y);d=I(1)+xx+yy
 return [I(max(-S,z.lo),min(S,z.hi),raw=True)for z in [2*x/d,2*y/d,sign*(I(1)-xx-yy)/d]]
def dot(a,b):
 z=sum((x*y for x,y in zip(a,b)),I(0))
 return I(max(-S,z.lo),min(S,z.hi),raw=True)
def run():
 result=json.loads((BASE/(P+'result.json')).read_text());nodes=json.loads((BASE/(P+'trace.json')).read_text())['nodes'];pending=json.loads((BASE/(P+'pending.json')).read_text())['nodes']
 assert BITS==384 and result['bits']==BITS
 assert result['claim_proved'] is False and result['status']=='budget_exhausted'
 for file,h in result['dependencies'].items():
  path=Path(file)
  if path.name==P+'bounded.py':path=BASE/(P+'runtime_source.py')
  assert hashlib.sha256(path.read_bytes()).hexdigest()==h,(file,h)
 assert len(nodes)==result['total_tree_nodes'] and [n['id']for n in nodes]==list(range(len(nodes)))
 assert [n['id']for n in pending]==[n['id']for n in nodes if n['action']=='pending']
 assert pending==[nodes[n['id']]for n in pending]
 parents=Counter();counts=Counter(n['action']for n in nodes);coverage=[Counter()for _ in range(4)]
 signs=[(1,1),(1,-1),(-1,1),(-1,-1)]
 u,v,t=map(F,result['T2_triangle_exact']);ui,vi,ti=map(I,(u,v,t));h=(I(1)-square(ui)).sqrt();g=I(1)+2*ui*vi*ti-square(ui)-square(vi)-square(ti)
 A=[[I(1),I(0),I(0)],[ui,h,I(0)],[vi,(ti-ui*vi)/h,g.sqrt()/h]];cap=I(F(14,25)).hi;rechecked=[]
 for n in nodes:
  assert n['root']in range(4) and tuple(n['signs'])==signs[n['root']]
  assert all(-S<=lo<hi<=S for lo,hi in n['box'])
  if n['parent']is None:
   assert n['id']==n['root'] and n['depth']==0 and n['box']==[[-S,S]]*4
  else:
   assert n['parent']<n['id'] and nodes[n['parent']]['depth']+1==n['depth']
  if n['action']=='split':
   ax=n['axis'];mid=int(n['midpoint_numerator']);assert mid==sum(n['box'][ax])//2 and len(n['children'])==2
   for side,cid in enumerate(n['children']):
    child=nodes[cid];parents[cid]+=1;assert child['parent']==n['id'] and child['root']==n['root']
    bb=[pair[:]for pair in n['box']];bb[ax]=[bb[ax][0],mid]if side==0 else[mid,bb[ax][1]];assert child['box']==bb
  else:
   vol=F(1)
   for lo,hi in n['box']:vol*=F(hi-lo,S)
   coverage[n['root']][n['action']]+=vol
   if n['action']=='exclude_pair_cap':
    q=chart(n['box'][:2],n['signs'][0]);r=chart(n['box'][2:],n['signs'][1]);ds=[dot(a,q)for a in A]+[dot(a,r)for a in A]+[dot(q,r)]
    z=ds[n['dot_index']];assert z.lo>cap and z.bounds()==n['dot'];rechecked.append(n['id'])
   elif n['action']=='accept_W':
    raise AssertionError('This structural audit does not independently verify positive W acceptance')
   else:assert n['action']=='pending'
 assert all(parents[i]==1 for i in range(4,len(nodes)))
 assert all(sum(c.values(),F(0))==16 for c in coverage)
 assert counts['pending']==result['pending']==len(pending) and counts['split']==result['counts']['split'] and counts['exclude_pair_cap']==result['counts']['excluded']
 assert len(nodes)-len(pending)==result['processed_nodes']
 assert [{k:str(v)for k,v in c.items()}for c in coverage]==[r['volume_by_action']for r in result['coverage']]
 diagnostic=[]
 for n in result['hardboxes']:
  diagnostic.append({'id':n['id'],'depth':n['depth'],'box_rational':[[str(F(a,S))for a in pair]for pair in n['box']],
    'coordinate_widths':[float(F(b-a,S))for a,b in n['box']],
    'max_input_dot_width':max(float(F(int(d['hi_numerator'])-int(d['lo_numerator']),S))for d in n['dot_intervals']),
    'max_residual_interval_width':float(F(int(n['residual_width_max_numerator']),S)),
    'W_lower':float(F(int(n['W_lower_numerator']),S))})
 out={'status':'partial_coverage_and_cap_rejections_verified','global_W_certificate':False,'checked_nodes':len(nodes),'checked_cap_exclusions':len(rechecked),'cap_exclusion_ids':rechecked,
  'accepted_W_leaves':counts['accept_W'],'pending':len(pending),'coverage':[{k:str(v)for k,v in c.items()}for c in coverage],
  'pending_by_root':dict(Counter(n['root']for n in pending)),'pending_by_depth':dict(Counter(n['depth']for n in pending)),
  'all_evaluated_W_lowers_zero':all(int(n['W_lower_numerator'])==0 for n in nodes if 'W_lower_numerator'in n),
  'root_max_residual_interval_width':[float(F(int(n['residual_width_max_numerator']),S))for n in result['root_diagnostics']],
  'hardbox_width_diagnostics':diagnostic,'run_source_hash':hashlib.sha256((BASE/(P+'runtime_source.py')).read_bytes()).hexdigest(),
  'current_source_hash':hashlib.sha256((BASE/(P+'bounded.py')).read_bytes()).hexdigest(),
  'source_difference':'After run, bounded.py gained only a no-Python-O guard. Runtime source is archived byte-for-byte; no rerun.',
  'warning':'This is a read-only structural and cap-rejection replay, not a closed W lower-bound certificate. All 2600 unresolved leaves remain unresolved.'}
 (BASE/(P+'audit.json')).write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({k:out[k]for k in ['status','checked_nodes','checked_cap_exclusions','accepted_W_leaves','pending','coverage','pending_by_root','pending_by_depth','all_evaluated_W_lowers_zero','root_max_residual_interval_width']},indent=2))
 return out
if __name__=='__main__':run()
