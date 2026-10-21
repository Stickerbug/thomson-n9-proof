#!/usr/bin/env python3
"""Data-only exact coverage/arithmetic audit. No polynomial/tensor evaluations."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import hashlib,json,time
if not __debug__:raise RuntimeError('Assertions required')
BASE=Path(__file__).resolve().parent;P='external_pair_interval2026_lowpair_';M=F(1,25000);HI=F(14,25);LO=F(-1)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run():
 clock=time.monotonic();up=BASE/(P+'universe.json');rp=BASE/(P+'result.json');fp=BASE/(P+'records.json');u=json.loads(up.read_text());r=json.loads(rp.read_text());d=json.loads(fp.read_text());cells=u['cells'];rows=d['records'];N=len(cells);phi=[F(x['phi_lower'])for x in cells];scale=1<<d['bits'];iscale=1<<d['I_bits']
 assert N==894 and r['complete_unordered_universe']==N*(N+1)//2
 for path,h in u['dependencies'].items():assert sha(Path(path))==h
 for path,h in r['dependencies'].items():assert sha(Path(path))==h
 def reason(i,j):
  if phi[i]+phi[j]>=5*M:return'phi_accept'
  if cells[i]['capacity_group']==cells[j]['capacity_group']:return'same_capacity_group_excluded'
  return'pending'
 initial=Counter();pending=[]
 for i in range(N):
  for j in range(i,N):
   why=reason(i,j);initial[why]+=1
   if why=='pending':pending.append((i,j))
 assert dict(initial)==u['initial_counts_unordered']
 assert [(x['i'],x['j'])for x in rows]==pending[:len(rows)]
 counts=Counter();covers=0;Wvalues=[]
 for row in rows:
  i,j=row['i'],row['j'];counts[row['action']]+=1;dots=row['dot_intervals'];bounds=[(F(int(z['lo_numerator']),1<<z['denominator_power_of_two']),F(int(z['hi_numerator']),1<<z['denominator_power_of_two']))for z in dots]
  assert len(dots)==7 and all(a<=b for a,b in bounds)
  assert F(row['phi_i_lower'])==phi[i]and F(row['phi_j_lower'])==phi[j]
  assert F(row['phi_part_lower'])==(phi[i]+phi[j])/5
  if row['action']=='exclude_pair_cap':assert bounds[row['dot_index']][0]>HI;continue
  assert all(a<=HI for a,b in bounds)
  inputs=[(max(LO,a),min(HI,b))for a,b in bounds];ls=[]
  for a,qr in enumerate(row['query_records']):
   box=[inputs[a],inputs[3+a],inputs[6]];paths=[c['path']for c in qr['cover']];mins=[];volume=F(0)
   for t,path in enumerate(paths):
    b=[(LO,HI)]*3
    for axis,side in path:
     assert axis in range(3)and side in [0,1];lo,hi=b[axis];mid=(lo+hi)/2;b[axis]=(lo,mid)if side==0 else(mid,hi)
    v=F(1)
    for (a0,b0),(lo,hi)in zip(b,box):
     low=max(a0,lo);high=min(b0,hi);assert low<=high;v*=high-low
    volume+=v;mins.append(int(qr['cover'][t]['lower_int']))
    for prior in paths[:t]:
     n=0
     while n<min(len(path),len(prior))and path[n]==prior[n]:n+=1
     assert n<min(len(path),len(prior)), 'overlapping ancestor paths'
     assert path[n][0]==prior[n][0]and path[n][1]!=prior[n][1], 'cover not a common subdivision tree'
   total=F(1)
   for lo,hi in box:total*=hi-lo
   assert volume==total and mins and min(mins)==int(qr['lower_int'])and len(paths)==qr['leaf_count']<=8 and qr['splits']<=30
   ls.append(max(0,min(mins)));covers+=1
  assert len(ls)==3 and ls==[int(v)for v in row['psi_lower_scaled']]
  W=(phi[i]+phi[j])/5+F(sum(ls),scale);assert W==F(row['W_lower_exact'])and M-W==F(row['threshold_minus_lower_exact'])
  assert (W>=M)==(row['action']=='accept_W');Wvalues.append(W)
 assert dict(counts)==r['counts']and r['visited_pairs']==len(rows)
 unvisited=len(pending)-len(rows);remaining=unvisited+counts['pending']
 assert unvisited==r['unvisited_inferred_pending']and remaining==r['final_pending_unordered']
 assert remaining+counts['accept_W']+counts['exclude_pair_cap']==initial['pending']
 assert r['next_unvisited_pair']==(list(pending[len(rows)])if len(rows)<len(pending)else None)
 out={'status':'exact_prefix_accounting_query_cover_and_arithmetic_verified','polynomial_evaluations':0,'coefficient_tensor_rebuilds':0,'cells':N,'initial_pending_unordered':len(pending),'visited_pairs':len(rows),'counts':dict(counts),'query_covers_checked':covers,'unvisited_inferred_pending':unvisited,'final_pending_unordered':remaining,'minimum_visited_W_lower_exact':str(min(Wvalues))if Wvalues else None,'minimum_visited_W_lower_display':float(min(Wvalues))if Wvalues else None,'query_coefficient_bound_reliance':'Stored exact outward Bernstein coefficient minima treated as supplied oracle data. Paths, rational input coverage, prefix, cap comparisons and final acceptance arithmetic independently checked; polynomial transform and de Casteljau tensors not rebuilt in this audit.','seconds':time.monotonic()-clock,'dependencies':{str(p):sha(p)for p in [up,rp,fp,Path(__file__)]}}
 (BASE/(P+'audit.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2));return out
if __name__=='__main__':run()
