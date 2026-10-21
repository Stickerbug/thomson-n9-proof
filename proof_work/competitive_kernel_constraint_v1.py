"""Exact necessary triple condition using a previously certified energy identity.
Prior global certificate is a dependency, not re-proved by this script.
"""
if not __debug__: raise RuntimeError('Assertions are required')
from fractions import Fraction as F
from pathlib import Path
from hashlib import sha256
import json
base=Path(__file__).parent
model=base/'nonsharp_d10_root25_7599205_v10.json'
report=base/'nonsharp_d10_root25_7599205_v10_result.json'
d=json.loads(model.read_text());verified=json.loads(report.read_text())
assert verified['status']=='certified'
B=F(d['target']);assert B==F('25.7599205')
U=F('25.75998653126983156407570227376049402866');threshold=7*(U-B)
poly={tuple(e):F(c)for e,c in d['residual_monomial']}
points=[('old_competitive_valley',['-.759220762336624','-.29211600772137486','.32931701954562287']),('new_pair_budget_boundary_valley',['.48071036383','.48071036393','.48071036395'])]
rows=[]
for name,strings in points:
 x=list(map(F,strings));pw=[[t**k for k in range(29)]for t in x]
 assert all(-1<=t<=F(14,25)for t in x)
 g=1+2*x[0]*x[1]*x[2]-sum(t*t for t in x);assert g>0
 val=sum(c*pw[0][a]*pw[1][b]*pw[2][c0]for (a,b,c0),c in poly.items());margin=threshold-val
 rows.append({'name':name,'point':strings,'Gram':str(g),'R_old':str(val),'C_kernel':str(margin),'excluded':margin<0,'display_only':float(margin)})
assert not rows[0]['excluded'] and rows[1]['excluded']
result={'status':'exact_necessary_condition_and_witnesses','scope':'Depends on prior certified residual nonnegativity and PSD kernel identity; no new energy bound or sharp Thomson proof.','B':str(B),'U':str(U),'threshold':str(threshold),'necessary_condition':'Each triangle of any E<=U configuration satisfies R_old<=7*(U-B).','proof':'E-B=sum_pairs(f-h)+(1/7)*sum_84_unordered_triples R_old+(1/6)*sum_729_ordered_triples F_old. All three terms are nonnegative, so each R_old<=7*(E-B)<=7*(U-B).','dependencies':{p.name:sha256(p.read_bytes()).hexdigest()for p in [model,report]},'witnesses':rows}
out=base/'competitive_kernel_constraint_v1.json'
if out.exists():assert json.loads(out.read_text())==result
else:out.write_text(json.dumps(result,indent=2)+'\n')
for row in rows:print(row['name'],'C_kernel=',row['display_only'],'excluded=',row['excluded'])
