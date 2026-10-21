#!/usr/bin/env python3
"""Finite low-cell pair prefix, exact phi cache and I384 -> int48 3D oracle.
Unvisited pair coverage is inferred from the explicitly saved complete universe.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import permutations
import json,hashlib,time,gc
from collections import Counter
import numpy as np
from dyadic_interval import I,S as SI,BITS as IBITS
from external_pair_interval2026_bounded import chart,dot,anchors
from exact_tensor_bernstein import coefficients
from certify_d4_int64 import safe_array,split64
if not __debug__:raise RuntimeError('Assertions required')
BASE=Path(__file__).resolve().parent
P='external_pair_interval2026_lowpair_'
BITS=48;S=1<<BITS;LO=F(-1);HI=F(14,25);M=F(1,25000)
class Cell:
 def __init__(self,b,box,path=()):self.b=b;self.box=box;self.path=path;self.children={}
def overlap(a,b):return all(max(x[0],y[0])<=min(x[1],y[1])for x,y in zip(a,b))
def split(c,ax,stats):
 if ax not in c.children:
  left,right=split64(c.b,ax);a,b=c.box[ax];mid=(a+b)/2;l=c.box[:];r=c.box[:];l[ax]=(a,mid);r[ax]=(mid,b)
  c.children[ax]=(Cell(left,l,c.path+((ax,0),)),Cell(right,r,c.path+((ax,1),)));stats['created_nodes']+=2;stats['resident_created_nodes']+=2
 return c.children[ax]
def query(root,box,deadline,stats,maxleaves=8,maxsplits=30):
 assert all(LO<=a<=b<=HI for a,b in box)
 cells=[root];n=0
 while n<maxsplits and time.monotonic()<deadline:
  choices=[]
  for k,c in enumerate(cells):
   for ax,(a,b)in enumerate(c.box):
    mid=(a+b)/2;lo=max(a,box[ax][0]);hi=min(b,box[ax][1]);single=hi<=mid or lo>=mid
    if single:choices.append((1,b-a,k,ax))
    elif len(cells)<maxleaves:
     variation=int(np.max(np.abs(np.diff(c.b,axis=ax))));choices.append((0,variation,k,ax))
  if not choices:break
  _,_,k,ax=max(choices);c=cells.pop(k);children=split(c,ax,stats);mid=sum(c.box[ax])/2
  if box[ax][1]<=mid:chosen=[children[0]]
  elif box[ax][0]>=mid:chosen=[children[1]]
  else:chosen=children
  cells.extend(ch for ch in chosen if overlap(ch.box,box));n+=1
 assert cells and len(cells)<=maxleaves
 lower=min(int(c.b.min())for c in cells)
 stats['queries']+=1;stats['splits']+=n
 cover=[{'path':[list(z)for z in c.path],'lower_int':str(int(c.b.min()))}for c in cells]
 return lower,{'lower_int':str(lower),'splits':n,'leaf_count':len(cells),'cover':cover}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(seconds=90,pair_limit=1000):
 start=time.monotonic();deadline=start+seconds
 for suffix in ['result.json','universe.json','records.json']:assert not(BASE/(P+suffix)).exists(),'refuse overwrite'
 up=BASE/'t2_unary_leaf_pair2026_result.json';cp=BASE/'t2_low_cells2026_capacity.json';bp=BASE/'t2_low_pair2026_combined_pruning.json';mp=BASE/'nonsharp_d10_root25_7599205_v10.json';rp=BASE/'nonsharp_d10_root25_7599205_v10_result.json';tp=BASE/'two_other_valleys2026_probe.json'
 unary=json.loads(up.read_text());cap=json.loads(cp.read_text());combined=json.loads(bp.read_text());model=json.loads(mp.read_text());report=json.loads(rp.read_text())
 assert report['status']=='certified'and report['pending']==0 and report['model_sha256']==sha(mp)
 assert combined['dependencies'][cp.name]==sha(cp)and combined['dependencies'][up.name]==sha(up)
 assert unary['source_sha256']==cap['dependencies'][str(BASE/'t2_unary_screen2026_result.json')]
 assert unary['threshold_W']==str(M)and cap['cell_count']==unary['cells']==894
 cells=unary['cell_bounds'];N=len(cells);phi=[F(c['phi_lower'])for c in cells];groups=[None]*N
 for j,(a,b)in enumerate(zip(cells,cap['cells'])):assert a['sign']==b['sign']and a['location']==b['location']
 for gr in cap['groups']:
  assert gr['capacity_one']and F(gr['diameter_squared_upper'])<F(22,25)
  for j in gr['cell_indices']:assert groups[j]is None;groups[j]=gr['label']
 assert all(g is not None for g in groups)
 def initial_reason(i,j):
  if phi[i]+phi[j]>=5*M:return 'phi_accept'
  if groups[i]==groups[j]:return 'same_capacity_group_excluded'
  return None
 init=Counter();ordered=Counter();remaining=0
 for i in range(N):
  for j in range(i,N):
   r=initial_reason(i,j)or'pending';init[r]+=1;ordered[r]+=1 if i==j else 2
 assert ordered['pending']==combined['remaining_ordered_pairs']==458584 and init['pending']==229292
 assert ordered['phi_accept']==combined['phi_pair_accepted']==303673
 assert ordered['same_capacity_group_excluded']+ordered['phi_accept']==combined['union_accepted_or_excluded']==340652
 universe={'cells':[{'id':j,**c,'capacity_group':groups[j]}for j,c in enumerate(cells)],'unordered_pairs':N*(N+1)//2,'complete_pair_universe':'all integer 0<=i<=j<894; no pending-file-only recovery','initial_skip_rule':'phi_i+phi_j>=1/5000 => accept; else same capacity_group => infeasible; else pending','initial_counts_unordered':dict(init),'initial_counts_ordered':dict(ordered),'dependencies':{str(p):sha(p)for p in [up,cp,bp]}}
 (BASE/(P+'universe.json')).write_text(json.dumps(universe,indent=2)+'\n')
 row=next(x for x in json.loads(tp.read_text())['results']if x['name']=='T2');A=anchors(*map(F,row['triangle_decimal']))
 q=[];ds=[]
 for c in cells:
  x,dx,y,dy=c['location'];aa=I(-1+F(2*x,1<<dx),-1+F(2*(x+1),1<<dx));bb=I(-1+F(2*y,1<<dy),-1+F(2*(y+1),1<<dy));qq=chart(aa,bb,c['sign']);q.append(qq);ds.append([dot(a,qq)for a in A])
 poly={tuple(e):F(v)for e,v in model['residual_monomial']}
 for p in permutations(range(3)):assert{tuple(e[p[i]]for i in range(3)):v for e,v in poly.items()}==poly
 root=Cell(safe_array(coefficients(poly,[(LO,HI)]*3,bits=BITS)),[(LO,HI)]*3)
 root_bounds=[str(int(root.b.min())),str(int(root.b.max()))];assert max(abs(int(x))for x in root.b.flat)<2**60
 stats=Counter(created_nodes=1,resident_created_nodes=1);records=[];counts=Counter();build_seconds=time.monotonic()-start;stopping=None;next_pair=None
 print('PREP',N,dict(init),'seconds',build_seconds,'root_bounds',root_bounds,flush=True)
 for i in range(N):
  if stopping:break
  for j in range(i,N):
   if initial_reason(i,j):continue
   if len(records)>=pair_limit:stopping='pair_limit';next_pair=[i,j];break
   if time.monotonic()>=deadline:stopping='time_limit';next_pair=[i,j];break
   begin=time.monotonic();dots=ds[i]+ds[j]+[dot(q[i],q[j])]
   rec={'i':i,'j':j,'phi_i_lower':str(phi[i]),'phi_j_lower':str(phi[j]),'phi_part_lower':str((phi[i]+phi[j])/5),'dot_intervals':[z.bounds()for z in dots]}
   bad=next((k for k,z in enumerate(dots)if 25*z.lo>14*SI),None)
   if bad is not None:rec.update(action='exclude_pair_cap',dot_index=bad);counts['exclude_pair_cap']+=1
   else:
    boxes=[(max(LO,F(z.lo,SI)),min(HI,F(z.hi,SI)))for z in dots];psi=[];queries=[]
    for a in range(3):
     lower,info=query(root,[boxes[a],boxes[3+a],boxes[6]],deadline,stats);psi.append(max(0,lower));queries.append(info)
    w=(phi[i]+phi[j])/5+F(sum(psi),S);action='accept_W'if w>=M else'pending'
    rec.update(action=action,psi_lower_scaled=[str(x)for x in psi],query_records=queries,W_lower_exact=str(w),W_lower_display=float(w),threshold_minus_lower_exact=str(M-w));counts[action]+=1
   rec['seconds']=time.monotonic()-begin;records.append(rec)
   if stats['resident_created_nodes']>1600:root.children.clear();stats['cache_resets']+=1;stats['resident_created_nodes']=1;gc.collect()
   if len(records)%100==0:print('PROGRESS',len(records),dict(counts),'seconds',time.monotonic()-start,flush=True)
 if stopping is None:stopping='all_initial_pending_visited'
 accepted=counts['accept_W'];excluded=counts['exclude_pair_cap'];visited=len(records);unvisited=init['pending']-visited;final_pending=unvisited+counts['pending']
 assert accepted+excluded+final_pending==init['pending']
 elapsed=time.monotonic()-start
 result={'status':'partial_prefix_coverage_not_T2_proof','claim_proved':False,'threshold_exact':str(M),'T2_triangle_exact':row['triangle_decimal'],'T2_budget_exact':row['budget_exact'],'fifteen_threshold_minus_budget_exact':str(15*M-F(row['budget_exact'])),'cells':N,'complete_unordered_universe':N*(N+1)//2,'initial_pending_unordered':init['pending'],'initial_pending_ordered':ordered['pending'],'visited_pairs':visited,'counts':dict(counts),'unvisited_inferred_pending':unvisited,'final_pending_unordered':final_pending,'next_unvisited_pair':next_pair,'prefix_rule':'lexicographic i,j with 0<=i<=j<894, skipping only archived exact phi-sum/capacity predicates','stopping_reason':stopping,'seconds_budget':seconds,'pair_budget':pair_limit,'elapsed_seconds':elapsed,'prepare_seconds':build_seconds,'bits':BITS,'I_bits':IBITS,'root_int_bounds':root_bounds,'root_shape':list(root.b.shape),'max_query_splits':30,'max_query_leaves':8,'stats':dict(stats),'arithmetic':'Exact rational root transform, downward int48; root |b|<2^60, every midpoint sum<2^61; all final W decisions Fraction. I384 chart/dots, exact cap compare. Query min over all retained overlapping leaves. max(0,psi) uses old geometric R certificate.','coverage':'Universe plus initial skip predicates plus records determines every pair; every unvisited initial-pending pair remains pending. No unlisted box removed. q/r symmetry uses exact polynomial permutation identity.','dependencies':{str(p):sha(p)for p in [up,cp,bp,mp,rp,tp,BASE/'dyadic_interval.py',BASE/'external_pair_interval2026_bounded.py',BASE/'exact_tensor_bernstein.py',BASE/'certify_d4_int64.py',Path(__file__)]},'warning':'Fixed rational T2 and supplied unary/capacity/global-R certificates only. Old global verifier and unary root polynomials not rerun. Not a Thomson exclusion proof; no SDP. Cached paths are hints for replay, each split must be recomputed outward.'}
 (BASE/(P+'records.json')).write_text(json.dumps({'bits':BITS,'I_bits':IBITS,'records':records},indent=2)+'\n')
 (BASE/(P+'result.json')).write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:result[k]for k in ['status','stopping_reason','elapsed_seconds','prepare_seconds','visited_pairs','counts','unvisited_inferred_pending','final_pending_unordered','next_unvisited_pair','stats']},indent=2),flush=True)
 return result
if __name__=='__main__':run()
