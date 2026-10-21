#!/usr/bin/env python3
"""At most 118s independent int48 coefficient replay plus exact query cover.
Rebuild root and lower split64 paths. All unfinished records remain unchecked.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import OrderedDict,Counter
import json,hashlib,time
from exact_tensor_bernstein import coefficients
from certify_d4_int64 import safe_array,split64
from dyadic_interval import I,S as SI,BITS as IBITS
from external_pair_interval2026_bounded import anchors,chart,dot
if not __debug__:raise RuntimeError('Assertions required')
BASE=Path(__file__).resolve().parent;P='external_pair_interval2026_lowpair_';LO=F(-1);HI=F(14,25);M=F(1,25000);BITS=48;S=1<<BITS
class Budget(Exception):pass
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(seconds=118,maxcache=1100):
 start=time.monotonic();deadline=start+seconds
 outpath=BASE/(P+'replay.json');assert not outpath.exists()
 rp=BASE/(P+'result.json');up=BASE/(P+'universe.json');fp=BASE/(P+'records.json');result=json.loads(rp.read_text());universe=json.loads(up.read_text());data=json.loads(fp.read_text());rows=data['records'];cells=universe['cells'];stats=Counter();verified=[]
 for p,h in result['dependencies'].items():assert sha(Path(p))==h
 for p,h in universe['dependencies'].items():assert sha(Path(p))==h
 mp=BASE/'nonsharp_d10_root25_7599205_v10.json';model=json.loads(mp.read_text());poly={tuple(e):F(c)for e,c in model['residual_monomial']};root=safe_array(coefficients(poly,[(LO,HI)]*3,bits=BITS));assert list(root.shape)==result['root_shape']and[int(root.min()),int(root.max())]==list(map(int,result['root_int_bounds']))
 buildtime=time.monotonic()-start;cache=OrderedDict();cache[()]=root
 def terminal(path):
  key=();arr=root
  for axis,side in path:
   if time.monotonic()>=deadline:raise Budget()
   nextkey=key+((axis,side),)
   if nextkey in cache:arr=cache.pop(nextkey);cache[nextkey]=arr;stats['cache_hits']+=1
   else:
    left,right=split64(arr,axis);stats['recomputed_splits']+=1
    for ss,child in enumerate((left,right)):
     ck=key+((axis,ss),)
     if ck in cache:cache.pop(ck)
     cache[ck]=child
    arr=left if side==0 else right
    while len(cache)>maxcache:
     ck,cv=cache.popitem(last=False)
     if ck==():cache[()]=cv
   key=nextkey
  stats['terminal_coefficient_minima_recomputed']+=1
  return int(arr.min())
 A=anchors(*map(F,result['T2_triangle_exact']));qcache={}
 def qbox(i):
  if i not in qcache:
   c=cells[i];x,dx,y,dy=c['location'];a=I(-1+F(2*x,1<<dx),-1+F(2*(x+1),1<<dx));b=I(-1+F(2*y,1<<dy),-1+F(2*(y+1),1<<dy));qq=chart(a,b,c['sign']);qcache[i]=(qq,[dot(v,qq)for v in A])
  return qcache[i]
 phi=[F(c['phi_lower'])for c in cells]
 def reason(i,j):return phi[i]+phi[j]>=5*M or cells[i]['capacity_group']==cells[j]['capacity_group']
 gen=((i,j)for i in range(len(cells))for j in range(i,len(cells))if not reason(i,j));counts=Counter();minW=None;incomplete=None
 try:
  for index,row in enumerate(rows):
   if time.monotonic()>=deadline:raise Budget()
   i,j=row['i'],row['j'];assert(i,j)==next(gen);qq,qd=qbox(i);rr,rd=qbox(j);dots=qd+rd+[dot(qq,rr)];assert[z.bounds()for z in dots]==row['dot_intervals'];stats['I384_pair_geometries_recomputed']+=1
   assert F(row['phi_i_lower'])==phi[i]and F(row['phi_j_lower'])==phi[j]
   if row['action']=='exclude_pair_cap':
    assert 25*dots[row['dot_index']].lo>14*SI
   else:
    boxes=[(max(LO,F(z.lo,SI)),min(HI,F(z.hi,SI)))for z in dots];lows=[]
    for a,query in enumerate(row['query_records']):
     if time.monotonic()>=deadline:raise Budget()
     box=[boxes[a],boxes[3+a],boxes[6]];active=[k for k,(lo,hi)in enumerate(box)if lo<hi];cover=query['cover'];volume=F(0);paths=[];mins=[]
     for c in cover:
      path=tuple(map(tuple,c['path']));bb=[(LO,HI)]*3
      for axis,side in path:
       assert axis in range(3)and side in [0,1];lo,hi=bb[axis];mid=(lo+hi)/2;bb[axis]=(lo,mid)if side==0 else(mid,hi)
      v=F(1)
      for k,((lo,hi),(x,y))in enumerate(zip(box,bb)):
       if k in active:
        low=max(lo,x);high=min(hi,y);assert low<=high;v*=high-low
       else:assert x<=lo<=y
      volume+=v
      for prior in paths:
       n=0
       while n<min(len(path),len(prior))and path[n]==prior[n]:n+=1
       assert n<min(len(path),len(prior))and path[n][0]==prior[n][0]and path[n][1]!=prior[n][1]
      paths.append(path);mn=terminal(path);assert mn==int(c['lower_int']);mins.append(mn)
     total=F(1)
     for k in active:total*=box[k][1]-box[k][0]
     assert volume==total and min(mins)==int(query['lower_int'])and len(mins)==query['leaf_count']<=8
     lows.append(max(0,min(mins)));stats['query_input_products_fully_replayed']+=1
    assert lows==list(map(int,row['psi_lower_scaled']))and len(lows)==3
    w=(phi[i]+phi[j])/5+F(sum(lows),S);assert w==F(row['W_lower_exact'])and M-w==F(row['threshold_minus_lower_exact']);assert(w>=M)==(row['action']=='accept_W')
    minW=w if minW is None else min(minW,w)
   counts[row['action']]+=1;verified.append([i,j])
   if len(verified)%100==0:print('REPLAY',len(verified),dict(counts),'seconds',time.monotonic()-start,flush=True)
 except Budget:
  incomplete={'record_index':len(verified),'pair':[rows[len(verified)]['i'],rows[len(verified)]['j']]if len(verified)<len(rows)else None}
 complete=len(verified)==len(rows)
 if complete:assert dict(counts)==result['counts']
 elapsed=time.monotonic()-start
 out={'status':'all_saved_pair_records_independently_replayed'if complete else'budget_exhausted_checked_prefix_only','all_records_replayed':complete,'saved_records':len(rows),'fully_checked_records':len(verified),'checked_counts':dict(counts),'unchecked_saved_records':len(rows)-len(verified),'interrupted_record':incomplete,'verified_prefix_pairs':verified,'seconds_budget':seconds,'elapsed_seconds':elapsed,'root_build_seconds':buildtime,'stats':dict(stats),'coefficient_bits':BITS,'I384_geometry_recomputed':True,'root_transform_rebuilt':True,'query_cover_check':'For each query, exact rational root paths recomputed using outward split64; terminal coefficient minima checked. Intersections cover the entire query interval product: disjoint projected interiors and equal exact projected volume; fixed axes require containment. All seven dot intervals rebuilt from I384 anchors/chart. Final cap and W Fraction decisions repeated.','minimum_checked_W_lower_exact':str(minW)if minW is not None else None,'remaining_global_pairs':result['final_pending_unordered'],'global_claim_proved':False,'reliance':'Archived unary phi lower bounds and capacity partition and old R>=0 certificate retained as dependencies. This replays the visited pair residual oracle and geometry, not the old 202923-node global R proof or unary degree54 roots.','dependencies':{str(p):sha(p)for p in [rp,up,fp,mp,BASE/'exact_tensor_bernstein.py',BASE/'certify_d4_int64.py',BASE/'dyadic_interval.py',BASE/'external_pair_interval2026_bounded.py',Path(__file__)]}}
 outpath.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k]for k in ['status','fully_checked_records','checked_counts','elapsed_seconds','root_build_seconds','stats','remaining_global_pairs']},indent=2),flush=True);return out
if __name__=='__main__':run()
