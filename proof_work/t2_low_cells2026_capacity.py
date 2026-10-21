"""Group all retained unary cells and strictly bound spherical group diameters.
Root coverage is inherited from the unary screen, not independently replayed here.
"""
if not __debug__:raise RuntimeError('Assertions required')
from pathlib import Path
from fractions import Fraction as F
import json,hashlib,time
import numpy as np
from certify_all_degree import I,S
BASE=Path(__file__).parent

def boxq(sign,loc):
 x,dx,y,dy=loc;a=I(-1+F(2*x,1<<dx),-1+F(2*(x+1),1<<dx));b=I(-1+F(2*y,1<<dy),-1+F(2*(y+1),1<<dy))
 # Squaring via product safely overestimates even intervals crossing zero.
 r=a*a+b*b;D=1+r;return [2*a/D,2*b/D,sign*(1-r)/D]
def run():
 start=time.monotonic();src=BASE/'t2_unary_screen2026_result.json';data=json.loads(src.read_text());probe=BASE/'two_other_valleys2026_probe.json';row=next(r for r in json.loads(probe.read_text())['results']if r['name']=='T2');centers=np.array([w['q']for w in row['wells'][:9]]);cells=[]
 for chart in data['results']:
  for leaf in chart['leaves']:
   if leaf['kind']not in ['low_pending','budget_pending']:continue
   assert leaf['kind']=='low_pending'
   sign=chart['sign'];x,dx,y,dy=leaf['location'];a=-1+float(F(2*x+1,1<<dx));b=-1+float(F(2*y+1,1<<dy));D=1+a*a+b*b;mid=np.array([2*a/D,2*b/D,sign*(1-a*a-b*b)/D]);group=int(np.argmax(centers@mid));bounds=boxq(sign,leaf['location']);cells.append({'sign':sign,'location':leaf['location'],'proposal_group':group,'coordinate_intervals':bounds})
 def certify(ids,label):
  lo=[min(cells[j]['coordinate_intervals'][k].lo for j in ids)for k in range(3)];hi=[max(cells[j]['coordinate_intervals'][k].hi for j in ids)for k in range(3)];d2=sum(F(b-a,S)**2 for a,b in zip(lo,hi));return {'label':label,'cell_indices':ids,'cell_count':len(ids),'coordinate_bounds':[[str(F(a,S)),str(F(b,S))]for a,b in zip(lo,hi)],'diameter_squared_upper':str(d2),'capacity_one':d2<F(22,25),'display_diameter_squared_upper':float(d2)}
 groups=[];initial=[]
 for g in range(len(centers)):
  ids=[j for j,c in enumerate(cells)if c['proposal_group']==g]
  if not ids:continue
  rec=certify(ids,str(g));initial.append(rec)
  stack=[rec]
  while stack:
   rec=stack.pop()
   if rec['capacity_one']:groups.append(rec);continue
   ids=rec['cell_indices'];assert len(ids)>1
   mids=np.array([[float(F(cells[j]['coordinate_intervals'][k].lo+cells[j]['coordinate_intervals'][k].hi,2*S))for k in range(3)]for j in ids]);axis=int(np.argmax(np.ptp(mids,axis=0)));order=np.argsort(mids[:,axis]);cut=len(ids)//2
   for k,part in enumerate([order[:cut],order[cut:]]):stack.append(certify([ids[int(z)]for z in part],rec['label']+'.'+str(k)))
 assigned=[j for g in groups for j in g['cell_indices']];assert sorted(assigned)==list(range(len(cells)))and len(assigned)==len(set(assigned));assert all(g['capacity_one']and g['cell_count']>0 for g in groups)
 serial=[{k:v for k,v in cell.items()if k!='coordinate_intervals'}for cell in cells]
 result={'status':'certified_capacity_one_group_cover_conditional_on_unary_root_cover','scope':'All saved unresolved rectangles covered exactly once by capacity-one groups; no pair-field or six-point exclusion claimed. Bounding boxes enclose full rectangles, including portions outside hemisphere disk.','cell_count':len(cells),'initial_group_count':len(initial),'initial_groups_failed_capacity':[g['label']for g in initial if not g['capacity_one']],'group_count':len(groups),'groups':groups,'cells':serial,'dependencies':{str(p):hashlib.sha256(p.read_bytes()).hexdigest()for p in [src,BASE/'t2_unary_screen2026.py',probe,BASE/'certify_all_degree.py',Path(__file__)]},'seconds':time.monotonic()-start};return result
if __name__=='__main__':
 result=run();out=BASE/'t2_low_cells2026_capacity.json';out.write_text(json.dumps(result,indent=2)+'\n');print('CELLS',result['cell_count'],'GROUPS',result['group_count'],'FAILED_INITIAL',result['initial_groups_failed_capacity']);print([(g['label'],g['cell_count'],g['display_diameter_squared_upper'])for g in result['groups']]);print('SAVED',out,'seconds',result['seconds'])
