#!/usr/bin/env python3
"""At most 20 saved nodes / 28 seconds: 2D+3D Bernstein range microbenchmark.
This never grows or accepts the 4D proof tree. All tensor arithmetic is exact/outward.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
import hashlib,json,time
import numpy as np
from exact_tensor_bernstein import coefficients
from certify_d4_int64 import split64,safe_array
if not __debug__:raise RuntimeError('Do not use Python -O')
BASE=Path(__file__).resolve().parent;P='external_pair_interval2026_';BITS=48;S=1<<BITS;LO=F(-1);HI=F(14,25)
class Cell:
 def __init__(self,b,u,box):self.b=b;self.u=u;self.box=box;self.children={}
def overlap(a,b):return all(max(x[0],y[0])<=min(x[1],y[1])for x,y in zip(a,b))
def build(poly,dim):return Cell(safe_array(coefficients(poly,[(LO,HI)]*dim,bits=BITS)),safe_array(coefficients(poly,[(LO,HI)]*dim,bits=BITS,upper=True)),[(LO,HI)]*dim)
def split(cell,axis,stats):
 if axis not in cell.children:
  l,r=split64(cell.b,axis);lu,ru=split64(cell.u,axis,upper=True);lo,hi=cell.box[axis];mid=(lo+hi)/2
  lb=cell.box[:];rb=cell.box[:];lb[axis]=(lo,mid);rb[axis]=(mid,hi)
  cell.children[axis]=(Cell(l,lu,lb),Cell(r,ru,rb));stats['created_cells']+=2
 return cell.children[axis]
def query(root,box,deadline,stats,maxleaves=4,maxsplits=10):
 cells=[root];splits=0
 while splits<maxsplits and time.monotonic()<deadline:
  choices=[]
  for i,c in enumerate(cells):
   for ax,(lo,hi)in enumerate(c.box):
    mid=(lo+hi)/2;clipped=(max(lo,box[ax][0]),min(hi,box[ax][1]));single=clipped[1]<=mid or clipped[0]>=mid
    if single:choices.append((1,float((hi-lo)/(HI-LO)),i,ax))
    elif len(cells)<maxleaves:
     variation=int(np.max(np.abs(np.diff(c.b,axis=ax))));choices.append((0,variation,i,ax))
  if not choices:break
  _,_,i,ax=max(choices);cell=cells.pop(i);children=split(cell,ax,stats);mid=sum(cell.box[ax])/2
  if box[ax][1]<=mid:chosen=[children[0]]
  elif box[ax][0]>=mid:chosen=[children[1]]
  else:chosen=children
  cells.extend(c for c in chosen if overlap(c.box,box));splits+=1
 lower=min(int(c.b.min())for c in cells);upper=max(int(c.u.max())for c in cells)
 stats['queries']+=1;stats['query_splits']+=splits
 return lower,upper,len(cells)
def run():
 assert not(BASE/(P+'bernstein_microbenchmark.json')).exists()
 clock=time.monotonic();deadline=clock+28
 result=json.loads((BASE/(P+'result.json')).read_text());trace=json.loads((BASE/(P+'trace.json')).read_text())['nodes'];modelpath=BASE/'nonsharp_d10_root25_7599205_v10.json'
 assert hashlib.sha256(modelpath.read_bytes()).hexdigest()==result['dependencies'][str(modelpath)]
 poly={tuple(a):F(v)for a,v in json.loads(modelpath.read_text())['residual_monomial']};deg=tuple(max(e[i]for e in poly)for i in range(3))
 full=build(poly,3);fixed=[]
 for edge in map(F,result['T2_triangle_exact']):
  d={}
  for(i,j,k),c in poly.items():d[(j,k)]=d.get((j,k),F(0))+c*edge**i
  fixed.append(build({e:c for e,c in d.items()if c},2))
 build_seconds=time.monotonic()-clock;stats={'created_cells':4,'queries':0,'query_splits':0};rows=[]
 ids=list(range(4))+[h['id']for h in result['hardboxes']]
 ids+=list(n['id']for n in trace[-80:]if'dot_intervals'in n)
 ids=list(dict.fromkeys(ids))[:20]
 if len(ids)<20:
  ids+=list(n['id']for n in reversed(trace)if'dot_intervals'in n and n['id']not in ids)[:20-len(ids)]
 for nid in ids:
  if time.monotonic()>=deadline:break
  n=trace[nid];boxes=[]
  for d in n['dot_intervals']:
   boxes.append((max(LO,F(int(d['lo_numerator']),1<<d['denominator_power_of_two'])),min(HI,F(int(d['hi_numerator']),1<<d['denominator_power_of_two']))))
  assert all(a<=b for a,b in boxes)
  p_low=[];p_up=[];widths=[];leaves=[];start=time.monotonic()
  for base in (0,3):
   for idx,(a,b)in enumerate(combinations(range(3),2)):
    l,u,c=query(fixed[idx],[boxes[base+a],boxes[base+b]],deadline,stats);p_low.append(max(0,l));p_up.append(max(0,u));widths.append((u-l)/S);leaves.append(c)
  ps=[];pu=[]
  for a in range(3):
   l,u,c=query(full,[boxes[a],boxes[3+a],boxes[6]],deadline,stats);ps.append(max(0,l));pu.append(max(0,u));widths.append((u-l)/S);leaves.append(c)
  wlo=(sum(p_low)//5+sum(ps))/S;whi=((sum(p_up)+4)//5+sum(pu))/S
  rows.append({'node':nid,'depth':n['depth'],'horner_max_residual_width':float(F(int(n['residual_width_max_numerator']),1<<384)),
    'bernstein_max_residual_width':max(widths),'bernstein_W_lower':wlo,'bernstein_W_upper':whi,'query_cover_leafcounts':leaves,'seconds':time.monotonic()-start,
    'threshold_passed_on_this_saved_box':sum(p_low)//5+sum(ps)>=(S+24999)//25000})
 out={'status':'microbenchmark_only','not_a_proof_run':True,'bits':BITS,'degree':deg,'full_tensor_shape':list(full.b.shape),'node_limit':20,'seconds_limit':28,'build_seconds':build_seconds,
  'elapsed_seconds':time.monotonic()-clock,'compared_nodes':len(rows),'rows':rows,'stats':stats,'max_query_leaves':4,'max_query_splits':10,
  'arithmetic':'Exact Fraction root transform; lower/upper integer coefficient bounds scaled 2^48. All midpoint de Casteljau outward. Safe int64 extrema asserted <2^60, each sum <2^61.',
  'query_coverage':'Each query keeps every child cell whose exact rational box overlaps its interval product; root starts with full [-1,14/25]^d. No uncovered portion is discarded. Min lower/max upper over intersecting leaves enclose R on the query. max(0,lower) uses the old geometric nonnegativity certificate only.',
  'warning':'Only saved nodes were compared; the original 2600 pending leaves are unchanged. No W acceptance is transferred to the proof tree. Boundaries may be duplicated and only worsen ranges.'}
 (BASE/(P+'bernstein_microbenchmark.json')).write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({k:out[k]for k in ['status','degree','full_tensor_shape','build_seconds','elapsed_seconds','compared_nodes','stats']},indent=2))
 print('ranges',[(r['node'],r['horner_max_residual_width'],r['bernstein_max_residual_width'],r['bernstein_W_lower'])for r in rows])
 return out
if __name__=='__main__':run()
