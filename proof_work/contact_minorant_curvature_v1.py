"""Enclose the f-H second derivative at the six true candidate nodes."""
from pathlib import Path
from fractions import Fraction as F
import json
from contact_minorant_factor_v1 import run,square,I,S,L,U
base=Path(__file__).parent
extra=[F(-1),F(-9,10),F(-2,5),F(-1,5),F(1,10),F(9,20),F(13,25),F(14,25)]
case=run(extra);saved=json.loads((base/'contact_minorant_factor_v1.json').read_text())['cases'][1]
assert case==saved
raw=lambda d:I(int(d['lo_numerator']),int(d['hi_numerator']),raw=True)
nodes=[raw(v)for v in case['newton_nodes'][::2]];K=raw(case['K_upper'])
r=I(L,U);candidate=[r*r/2-1,-r,I('-0.5'),2*r*r-1,1-I('1.5')*r*r,r/2]
rows=[]
for x in candidate:
 matches=[i for i,z in enumerate(nodes)if z.lo==x.lo and z.hi==x.hi];assert len(matches)==1
 j=matches[0];bound=2*K
 for k,z in enumerate(nodes):
  if k!=j:bound=bound*square(x-z)
 assert bound.lo>0
 rows.append({'node':x.bounds(),'curvature_upper':bound.bounds(),'display_only':float(F(bound.hi,S))})
result={'status':'certified_upper_bounds','formula':'0 < (f-H)second(t_j) = 2*K(t_j)*product_{i!=j}(t_j-t_i)^2 <= saved curvature_upper; K(t_j)<=K(57/100).','candidate_nodes':rows,'scope':'Diagonal Hessian correction for replacing sum f by sum H at candidate triples; no residual Hessian or global Thomson certificate.'}
out=base/'contact_minorant_curvature_v1.json'
if out.exists():assert json.loads(out.read_text())==result
else:out.write_text(json.dumps(result,indent=2)+'\n')
print('Candidate f-H curvature upper bounds:',[row['display_only']for row in rows])
