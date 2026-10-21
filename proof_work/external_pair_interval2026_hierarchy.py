#!/usr/bin/env python3
"""One finite hierarchical ordered product attempt, exact IDs and int48 oracle.
No pending or unvisited ordered pair is removed from the explicit N^2 universe.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import permutations
from collections import Counter
import heapq,json,hashlib,time,gc
import numpy as np
from dyadic_interval import I,S as SI,BITS as IBITS
from external_pair_interval2026_bounded import anchors,chart,dot
from external_pair_interval2026_lowpair_batch import Cell,query
from exact_tensor_bernstein import coefficients
from certify_d4_int64 import safe_array
if not __debug__:raise RuntimeError('Assertions required')
BASE=Path(__file__).resolve().parent;P='external_pair_interval2026_hierarchy_';M=F(1,25000);HI=F(14,25);LO=F(-1);BITS=48;S=1<<BITS
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(seconds=118,block_limit=3000):
 start=time.monotonic();deadline=start+seconds
 for suffix in ['result.json','tree.json','blocks.json','frontier.json']:assert not(BASE/(P+suffix)).exists(),'refuse overwrite'
 up=BASE/'external_pair_interval2026_lowpair_universe.json';prp=BASE/'external_pair_interval2026_lowpair_replay.json';tp=BASE/'two_other_valleys2026_probe.json';mp=BASE/'nonsharp_d10_root25_7599205_v10.json';rp=BASE/'nonsharp_d10_root25_7599205_v10_result.json';u=json.loads(up.read_text());prior=json.loads(prp.read_text());model=json.loads(mp.read_text());report=json.loads(rp.read_text())
 assert prior['all_records_replayed']and prior['fully_checked_records']==487
 for p,h in prior['dependencies'].items():assert sha(Path(p))==h
 for p,h in u['dependencies'].items():assert sha(Path(p))==h
 assert report['status']=='certified'and report['pending']==0 and report['model_sha256']==sha(mp)
 cells=u['cells'];N=len(cells);assert N==894
 row=next(x for x in json.loads(tp.read_text())['results']if x['name']=='T2');A=anchors(*map(F,row['triangle_decimal']))
 phi=[F(c['phi_lower'])for c in cells];q=[];ad=[]
 for c in cells:
  x,dx,y,dy=c['location'];a=I(-1+F(2*x,1<<dx),-1+F(2*(x+1),1<<dx));b=I(-1+F(2*y,1<<dy),-1+F(2*(y+1),1<<dy));qq=chart(a,b,c['sign']);q.append(qq);ad.append([dot(v,qq)for v in A])
 nodes=[]
 def build(ids,sign,parent=None):
  node={'id':len(nodes),'ids':sorted(ids),'sign':sign,'parent':parent,'phi':min(phi[i]for i in ids),'labels':sorted(set(cells[i]['capacity_group']for i in ids)),
   'q':[I(min(q[i][a].lo for i in ids),max(q[i][a].hi for i in ids),raw=True)for a in range(3)],
   'ad':[I(min(ad[i][a].lo for i in ids),max(ad[i][a].hi for i in ids),raw=True)for a in range(3)]}
  nodes.append(node)
  if len(ids)>1:
   ax=max(range(3),key=lambda a:max(q[i][a].lo+q[i][a].hi for i in ids)-min(q[i][a].lo+q[i][a].hi for i in ids));order=sorted(ids,key=lambda i:(q[i][ax].lo+q[i][ax].hi,i));cut=len(ids)//2
   node['partition_axis_heuristic']=ax;node['children']=[build(order[:cut],sign,node['id']),build(order[cut:],sign,node['id'])]
  else:node['children']=[]
  return node['id']
 chartroots=[build([i for i,c in enumerate(cells)if c['sign']==s],s)for s in [1,-1]]
 assert sorted(i for r in chartroots for i in nodes[r]['ids'])==list(range(N))
 for n in nodes:
  if n['children']:
   a,b=map(lambda k:nodes[k]['ids'],n['children']);assert not set(a)&set(b)and sorted(a+b)==n['ids']
 poly={tuple(e):F(v)for e,v in model['residual_monomial']}
 for p in permutations(range(3)):assert{tuple(e[p[i]]for i in range(3)):v for e,v in poly.items()}==poly
 root=Cell(safe_array(coefficients(poly,[(LO,HI)]*3,bits=BITS)),[(LO,HI)]*3)
 stats=Counter(created_nodes=1,resident_created_nodes=1);blocks=[];todo=[];roots=[];memo={};counts=Counter();processed=0
 def addblock(a,b,parent=None):
  k=len(blocks);n={'id':k,'parent':parent,'left_node':a,'right_node':b,'ordered_pair_count':len(nodes[a]['ids'])*len(nodes[b]['ids'])};blocks.append(n);heapq.heappush(todo,(-n['ordered_pair_count'],k));return k
 for a in chartroots:
  for b in chartroots:roots.append(addblock(a,b))
 build_seconds=time.monotonic()-start;print('PREP',N,'nodes',len(nodes),'seconds',build_seconds,flush=True)
 while todo and processed<block_limit and time.monotonic()<deadline:
  _,bid=heapq.heappop(todo);bl=blocks[bid];a,b=bl['left_node'],bl['right_node'];na,nb=nodes[a],nodes[b];processed+=1
  base=(na['phi']+nb['phi'])/5;bl['phi_part_lower']=str(base);action=None
  if base>=M:action='accept_phi'
  elif len(set(na['labels']+nb['labels']))==1:action='exclude_capacity'
  else:
   ca,cb=sorted([a,b]);canon=nodes[ca],nodes[cb];dots=canon[0]['ad']+canon[1]['ad']+[dot(canon[0]['q'],canon[1]['q'])];bad=next((k for k,z in enumerate(dots)if 25*z.lo>14*SI),None)
   bl['canonical_query_nodes']=[ca,cb];bl['dot_intervals']=[z.bounds()for z in dots]
   if bad is not None:action='exclude_pair_cap';bl['dot_index']=bad
   else:
    key=(ca,cb)
    if key in memo:
     source=memo[key];w=F(blocks[source]['W_lower_exact']);bl.update(psi_certificate_from=source,W_lower_exact=str(w))
    else:
     ib=[(max(LO,F(z.lo,SI)),min(HI,F(z.hi,SI)))for z in dots];psi=[];cert=[]
     coarse=max(hi-lo for lo,hi in ib)>F(1,2)
     for k in range(3):
      if base+F(sum(psi),S)>=M:psi.append(0);cert.append({'geometric_nonnegative_only':True});continue
      l,info=query(root,[ib[k],ib[3+k],ib[6]],deadline,stats,maxleaves=8,maxsplits=0 if coarse else 30);psi.append(max(0,l));info['maxsplits_used']=0 if coarse else 30;cert.append(info)
     w=base+F(sum(psi),S);bl.update(psi_lower_scaled=[str(x)for x in psi],query_records=cert,W_lower_exact=str(w),W_lower_display=float(w),coarse_zero_split_query=coarse);memo[key]=bid
    if w>=M:action='accept_psi'
  if action is None:
   if na['children']or nb['children']:
    if not nb['children']:side=0
    elif not na['children']:side=1
    else:side=0 if len(na['ids'])>=len(nb['ids'])else 1
    ch=na['children']if side==0 else nb['children'];bl.update(action='split',split_side=side,children=[addblock(c,b,bid)if side==0 else addblock(a,c,bid)for c in ch]);counts['split']+=1
   else:action='pending_single_cell'
  if action is not None:
   bl['action']=action;bl['left_ids']=na['ids'];bl['right_ids']=nb['ids'];counts[action]+=1
  if stats['resident_created_nodes']>1400:root.children.clear();stats['resident_created_nodes']=1;stats['cache_resets']+=1;gc.collect()
  if processed%200==0:print('BLOCKS',processed,'frontier',len(todo),dict(counts),'seconds',time.monotonic()-start,flush=True)
 reason='all_blocks_processed'if not todo else'block_limit'if processed>=block_limit else'time_limit'
 pending_stack=[k for _,k in todo]
 for k in pending_stack:
  bl=blocks[k];bl.update(action='pending_budget',left_ids=nodes[bl['left_node']]['ids'],right_ids=nodes[bl['right_node']]['ids']);counts['pending_budget']+=1
 mask=np.zeros((N,N),dtype=np.uint16);weighted=Counter();terminal=[]
 for bl in blocks:
  if bl['action']=='split':continue
  terminal.append(bl['id']);ids=bl['left_ids'];jds=bl['right_ids'];assert len(ids)*len(jds)==bl['ordered_pair_count'];mask[np.ix_(ids,jds)]+=1;weighted[bl['action']]+=bl['ordered_pair_count']
 assert int(mask.min())==int(mask.max())==1 and sum(weighted.values())==N*N
 for bl in blocks:
  if bl['action']=='split':
   c0,c1=(blocks[k]for k in bl['children']);assert c0['parent']==c1['parent']==bl['id']and c0['ordered_pair_count']+c1['ordered_pair_count']==bl['ordered_pair_count']
 serialized=[]
 for n in nodes:
  serialized.append({'id':n['id'],'ids':n['ids'],'sign':n['sign'],'parent':n['parent'],'children':n['children'],'phi_lower_exact':str(n['phi']),'capacity_labels':n['labels'],'coordinate_intervals':[z.bounds()for z in n['q']],'anchor_dot_intervals':[z.bounds()for z in n['ad']],'partition_axis_heuristic':n.get('partition_axis_heuristic')})
 pending_pairs=weighted['pending_budget']+weighted['pending_single_cell'];elapsed=time.monotonic()-start
 result={'status':'partial_hierarchical_low_pair_domain'if pending_pairs else'low_pair_domain_closed_conditional_on_dependencies','global_T2_proof':False,'threshold_exact':str(M),'T2_triangle_exact':row['triangle_decimal'],'T2_budget_exact':row['budget_exact'],'cells':N,'ordered_pair_universe':N*N,'chart_root_nodes':chartroots,'product_roots':roots,'low_set_tree_nodes':len(nodes),'processed_blocks':processed,'total_product_blocks':len(blocks),'terminal_blocks':len(terminal),'counts_blocks':dict(counts),'counts_ordered_pairs':dict(weighted),'pending_ordered_pairs':pending_pairs,'pending_stack_blocks':len(pending_stack),'processed_block_budget':block_limit,'seconds_budget':seconds,'elapsed_seconds':elapsed,'prepare_seconds':build_seconds,'stopping_reason':reason,'bits':BITS,'I_bits':IBITS,'root_int_bounds':[str(int(root.b.min())),str(int(root.b.max()))],'root_shape':list(root.b.shape),'max_query_splits':30,'max_query_leaves':8,'stats':dict(stats),'memoized_oracle_blocks':len(memo),'mask_min':int(mask.min()),'mask_max':int(mask.max()),'coverage':'All four ordered chart products start at complete 894x894 universe. Every split replaces one ID set by disjoint exhaustive children. Terminal ID products including every budget pending block mark every ordered cell pair exactly once. Nonconnected set bboxes enclose unions.','query_policy':'The old independent-replayed lower-only 3D int48 oracle is reused. Boxes with width>1/2 may use zero splits (valid coarse lower), forcing partition if insufficient. Once a partial psi sum reaches threshold, remaining psi terms use old R>=0. Canonical node-pair memo uses exact R permutation symmetry.','warning':'Fixed rational T2 low cells only. Unary/root coverage/capacity/global R proofs are dependencies. Pending blocks remain unresolved; no true-root or neighborhood assertion. No new SDP, no repeated prefix run.','dependencies':{str(p):sha(p)for p in [up,prp,tp,mp,rp,BASE/'dyadic_interval.py',BASE/'external_pair_interval2026_bounded.py',BASE/'external_pair_interval2026_lowpair_batch.py',BASE/'exact_tensor_bernstein.py',BASE/'certify_d4_int64.py',Path(__file__)]}}
 (BASE/(P+'tree.json')).write_text(json.dumps({'cells':cells,'chart_root_nodes':chartroots,'nodes':serialized},indent=2)+'\n');(BASE/(P+'blocks.json')).write_text(json.dumps({'product_roots':roots,'blocks':blocks},indent=2)+'\n');(BASE/(P+'frontier.json')).write_text(json.dumps({'pending_stack_blocks':pending_stack,'pending_single_cell_blocks':[b['id']for b in blocks if b['action']=='pending_single_cell'],'terminal_blocks':terminal,'restart_rule':'Reconstruct all four roots and explicit terminal/parent partitions from complete tree+blocks, never infer resolved status from frontier file alone.'},indent=2)+'\n');(BASE/(P+'result.json')).write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:result[k]for k in ['status','processed_blocks','total_product_blocks','counts_blocks','counts_ordered_pairs','pending_ordered_pairs','elapsed_seconds','prepare_seconds','stopping_reason','stats']},indent=2),flush=True);return result
if __name__=='__main__':run()
