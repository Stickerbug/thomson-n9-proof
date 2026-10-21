"""Numerical conflict graph on discovered wells; not an exhaustive sphere proof."""
from pathlib import Path
from itertools import combinations
import json,numpy as np
BASE=Path(__file__).parent
rows=json.loads((BASE/'two_other_valleys2026_probe.json').read_text())['results'];out=[]
for row in rows:
 wells=row['wells'];q=np.array([z['q']for z in wells]);cost=np.array([z['phi']for z in wells]);dots=q@q.T;conflict=dots>.56;best=None;maxind=0
 for n in range(1,min(6,len(q))+1):
  for inds in combinations(range(len(q)),n):
   if any(conflict[i,j]for i,j in combinations(inds,2)):continue
   maxind=max(maxind,n)
   if n==6 and(best is None or sum(cost[list(inds)])<best['cost']):best={'indices':list(inds),'cost':float(sum(cost[list(inds)])),'max_pair_dot':float(max(dots[i,j]for i,j in combinations(inds,2))),'q':q[list(inds)].tolist()}
 rec={'triangle':row['name'],'well_count':len(q),'pair_dot_matrix':dots.tolist(),'conflict_pairs':[[i,j]for i,j in combinations(range(len(q)),2)if conflict[i,j]],'largest_independent_set_capped_at6':maxind,'best_six_discovered_wells':best,'budget':row['budget_display']};out.append(rec);print(json.dumps(rec),flush=True)
path=BASE/'two_other_valleys2026_well_graph.json';path.write_text(json.dumps({'status':'numerical_discovery_only','rows':out},indent=2)+'\n');print('SAVED',path)
