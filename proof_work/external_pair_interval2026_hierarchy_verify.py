#!/usr/bin/env python3
"""Independent ID-product geometry/coverage/Fraction audit, no new tensor work."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import json,hashlib,time
import numpy as np
from dyadic_interval import I,S as SI
from external_pair_interval2026_bounded import anchors,chart,dot
if not __debug__:raise RuntimeError('Assertions required')
BASE=Path(__file__).resolve().parent;P='external_pair_interval2026_hierarchy_';M=F(1,25000);HI=F(14,25);LO=F(-1)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def unpack(d):return I(int(d['lo_numerator']),int(d['hi_numerator']),raw=True)
def input_box(z):return max(LO,F(z.lo,SI)),min(HI,F(z.hi,SI))
def cover_check(record,box):
 cover=record['cover'];volume=F(0);paths=[];mins=[];active=[k for k,(a,b)in enumerate(box)if a<b]
 for c in cover:
  path=c['path'];bb=[(LO,HI)]*3
  for axis,side in path:
   assert axis in range(3)and side in [0,1];a,b=bb[axis];mid=(a+b)/2;bb[axis]=(a,mid)if side==0 else(mid,b)
  v=F(1)
  for k,((a,b),(x,y))in enumerate(zip(box,bb)):
   if k in active:low=max(a,x);high=min(b,y);assert low<=high;v*=high-low
   else:assert x<=a<=y
  volume+=v
  for prior in paths:
   n=0
   while n<min(len(path),len(prior))and path[n]==prior[n]:n+=1
   assert n<min(len(path),len(prior))and path[n][0]==prior[n][0]and path[n][1]!=prior[n][1]
  paths.append(path);mins.append(int(c['lower_int']))
 total=F(1)
 for k in active:total*=box[k][1]-box[k][0]
 assert total==volume and min(mins)==int(record['lower_int'])and len(paths)==record['leaf_count']<=8 and record['splits']<=30
 return max(0,min(mins))
def run():
 start=time.monotonic();rp=BASE/(P+'result.json');tp=BASE/(P+'tree.json');bp=BASE/(P+'blocks.json');fp=BASE/(P+'frontier.json');result=json.loads(rp.read_text());tree=json.loads(tp.read_text());blocks=json.loads(bp.read_text())['blocks'];frontier=json.loads(fp.read_text());cells=tree['cells'];nodes=tree['nodes'];N=len(cells);assert N==894
 for p,h in result['dependencies'].items():assert sha(Path(p))==h
 u=json.loads((BASE/'external_pair_interval2026_lowpair_universe.json').read_text());assert cells==u['cells']
 A=anchors(*map(F,result['T2_triangle_exact']));phi=[F(c['phi_lower'])for c in cells];q=[];ad=[]
 for c in cells:
  x,dx,y,dy=c['location'];a=I(-1+F(2*x,1<<dx),-1+F(2*(x+1),1<<dx));b=I(-1+F(2*y,1<<dy),-1+F(2*(y+1),1<<dy));qq=chart(a,b,c['sign']);q.append(qq);ad.append([dot(v,qq)for v in A])
 seen_nodes=Counter();roots=tree['chart_root_nodes'];assert sorted(i for r in roots for i in nodes[r]['ids'])==list(range(N))
 for n in nodes:
  assert n['id']in range(len(nodes))and n is nodes[n['id']];ids=n['ids'];assert ids==sorted(set(ids))and ids and all(cells[i]['sign']==n['sign']for i in ids)
  assert F(n['phi_lower_exact'])==min(phi[i]for i in ids)and n['capacity_labels']==sorted(set(cells[i]['capacity_group']for i in ids))
  expected_q=[I(min(q[i][k].lo for i in ids),max(q[i][k].hi for i in ids),raw=True).bounds()for k in range(3)];expected_ad=[I(min(ad[i][k].lo for i in ids),max(ad[i][k].hi for i in ids),raw=True).bounds()for k in range(3)]
  assert expected_q==n['coordinate_intervals']and expected_ad==n['anchor_dot_intervals']
  if n['children']:
   a,b=[nodes[k]for k in n['children']];assert not set(a['ids'])&set(b['ids'])and sorted(a['ids']+b['ids'])==ids and a['parent']==b['parent']==n['id'];seen_nodes.update(n['children'])
  else:assert len(ids)==1
 assert all(seen_nodes[k]==(0 if k in roots else 1)for k in range(len(nodes)))
 product_roots=result['product_roots'];assert [(blocks[k]['left_node'],blocks[k]['right_node'])for k in product_roots]==[(a,b)for a in roots for b in roots]
 mask=np.zeros((N,N),dtype=np.uint16);weighted=Counter();actions=Counter();child_seen=Counter();terminals=[];query_count=0;memo_count=0
 for bl in blocks:
  k=bl['id'];assert bl is blocks[k];a,b=nodes[bl['left_node']],nodes[bl['right_node']];ids,jds=a['ids'],b['ids'];assert bl['ordered_pair_count']==len(ids)*len(jds);base=(F(a['phi_lower_exact'])+F(b['phi_lower_exact']))/5
  if bl['action']!='pending_budget':assert F(bl['phi_part_lower'])==base
  if bl['action']=='split':
   cs=[blocks[z]for z in bl['children']];assert len(cs)==2 and all(c['parent']==k for c in cs);side=bl['split_side'];expected=[(c,b['id'])for c in a['children']]if side==0 else[(a['id'],c)for c in b['children']];assert[(c['left_node'],c['right_node'])for c in cs]==expected;child_seen.update(bl['children']);continue
  terminals.append(k);assert bl['left_ids']==ids and bl['right_ids']==jds;mask[np.ix_(ids,jds)]+=1;weighted[bl['action']]+=len(ids)*len(jds);actions[bl['action']]+=1
  if bl['action']=='pending_budget':continue
  if bl['action']=='accept_phi':assert base>=M;continue
  if bl['action']=='exclude_capacity':assert len(set(a['capacity_labels']+b['capacity_labels']))==1;continue
  ca,cb=bl['canonical_query_nodes'];assert[ca,cb]==sorted([a['id'],b['id']]);na,nb=nodes[ca],nodes[cb];dots=[unpack(x)for x in na['anchor_dot_intervals']]+[unpack(x)for x in nb['anchor_dot_intervals']]+[dot(list(map(unpack,na['coordinate_intervals'])),list(map(unpack,nb['coordinate_intervals'])))];assert[z.bounds()for z in dots]==bl['dot_intervals']
  if bl['action']=='exclude_pair_cap':assert 25*dots[bl['dot_index']].lo>14*SI;continue
  if 'psi_certificate_from'in bl:
   src=blocks[bl['psi_certificate_from']];assert src['id']<k and src['canonical_query_nodes']==bl['canonical_query_nodes']and src['phi_part_lower']==bl['phi_part_lower'];assert src['W_lower_exact']==bl['W_lower_exact'];memo_count+=1
  else:
   ib=list(map(input_box,dots));ls=[]
   for j,c in enumerate(bl['query_records']):
    if c.get('geometric_nonnegative_only'):ls.append(0);continue
    ls.append(cover_check(c,[ib[j],ib[3+j],ib[6]]));query_count+=1
   assert ls==list(map(int,bl['psi_lower_scaled']))and len(ls)==3;w=base+F(sum(ls),1<<result['bits']);assert w==F(bl['W_lower_exact'])
  assert(F(bl['W_lower_exact'])>=M)==(bl['action']=='accept_psi')
 assert all(child_seen[k]==(0 if k in product_roots else 1)for k in range(len(blocks)))
 assert int(mask.min())==int(mask.max())==1 and sum(weighted.values())==N*N and dict(weighted)==result['counts_ordered_pairs'];assert sorted(terminals)==sorted(frontier['terminal_blocks']);assert sorted(frontier['pending_stack_blocks'])==sorted(b['id']for b in blocks if b['action']=='pending_budget');assert sorted(frontier['pending_single_cell_blocks'])==sorted(b['id']for b in blocks if b['action']=='pending_single_cell')
 pending=weighted['pending_budget']+weighted['pending_single_cell'];assert pending==result['pending_ordered_pairs']
 initial=np.zeros((N,N),dtype=bool);resolved=np.zeros((N,N),dtype=bool)
 for i in range(N):
  for j in range(i,N):
   yes=phi[i]+phi[j]>=5*M or cells[i]['capacity_group']==cells[j]['capacity_group'];initial[i,j]=initial[j,i]=yes
 for bl in blocks:
  if bl['action']not in ['split','pending_budget','pending_single_cell']:resolved[np.ix_(bl['left_ids'],bl['right_ids'])]=True
 initial_count=int(initial.sum());hierarchy_count=int(resolved.sum());overlap=int((initial&resolved).sum());new_count=int((resolved&~initial).sum());union_count=int((initial|resolved).sum());assert initial_count==340652 and union_count==initial_count+new_count
 union_metrics={'initial_resolved_ordered_pairs':initial_count,'hierarchy_resolved_ordered_pairs':hierarchy_count,'overlap_resolved_ordered_pairs':overlap,'new_resolved_ordered_pairs_beyond_initial':new_count,'union_resolved_ordered_pairs':union_count,'union_pending_ordered_pairs':N*N-union_count,'warning':'Compare against initial pruning by union; hierarchical budget-pending products may contain many previously resolved individual pairs.'}
 out={'status':'entire_hierarchical_ID_product_geometry_and_arithmetic_audited','union_with_initial_pruning':union_metrics,'cells':N,'tree_nodes_checked':len(nodes),'product_blocks_checked':len(blocks),'terminal_blocks':len(terminals),'query_covers_checked':query_count,'canonical_reuses_checked':memo_count,'mask_min':int(mask.min()),'mask_max':int(mask.max()),'ordered_pair_universe':N*N,'counts_ordered_pairs':dict(weighted),'pending_ordered_pairs':pending,'polynomial_evaluations':0,'coefficient_tensor_rebuilds':0,'warning':'Exact ID/cartesian coverage, all I384 node geometry, bounds arithmetic and query cover verified. New query coefficient minima remain supplied oracle data generated by the already separately tested source; no new terminal coefficient replay in this audit. Global T2 remains unresolved.','seconds':time.monotonic()-start,'dependencies':{str(p):sha(p)for p in [rp,tp,bp,fp,Path(__file__)]}}
 (BASE/(P+'audit.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2));return out
if __name__=='__main__':run()
