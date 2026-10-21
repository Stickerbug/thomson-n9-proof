"""Strict counterexamples to six-phi exclusion, NOT to the Thomson conjecture."""
if not __debug__:raise RuntimeError('Assertions must be enabled')
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
import json,hashlib
from certify_all_degree import I,S
BASE=Path(__file__).parent
modelpath=BASE/'nonsharp_d10_root25_7599205_v10.json';model=json.loads(modelpath.read_text());terms=[(tuple(e),I(F(z)))for e,z in model['residual_monomial']]
probe=json.loads((BASE/'two_other_valleys2026_probe.json').read_text())['results'];graphs=json.loads((BASE/'two_other_valleys2026_well_graph.json').read_text())['rows'];budget=json.loads((BASE/'fixed_triangle_two_cap_budget_exact_v1.json').read_text());U=F(budget['U']);B=F(model['target'])
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def R(x,y,z):
 powers=[]
 for a in [x,y,z]:
  row=[I(1)]
  for _ in range(27):row.append(row[-1]*a)
  powers.append(row)
 return sum(c*powers[0][i]*powers[1][j]*powers[2][k]for (i,j,k),c in terms)
rows=[]
for data,graph in zip(probe,graphs):
 u,v,t=map(F,data['triangle_decimal']);gram=1+2*u*v*t-u*u-v*v-t*t;s=I(1-u*u).sqrt()
 A=[[I(1),I(0),I(0)],[I(u),s,I(0)],[I(v),I(t-u*v)/s,I(gram).sqrt()/s]]
 points=[]
 for q in graph['best_six_discovered_wells']['q']:
  q=list(map(lambda z:F(str(z)),q));x=q[0]/(1+q[2]);y=q[1]/(1+q[2]);D=1+x*x+y*y
  p=[2*x/D,2*y/D,(1-x*x-y*y)/D];assert dot(p,p)==1;points.append(p)
 pairmax=max(dot(a,b)for a,b in combinations(points,2));assert pairmax<F(14,25)
 ip=[[dot(a,p)for a in A]for p in points];assert max(z.hi for row in ip for z in row)<I(F(14,25)).lo
 phi=[R(I(u),row[0],row[1])+R(I(v),row[0],row[2])+R(I(t),row[1],row[2])for row in ip];total=sum(phi);K=7*(I(U)-I(B))-R(I(u),I(v),I(t));assert total.hi<K.lo
 allpoints=A+[[I(x)for x in p]for p in points];energy=sum((2-2*dot(a,b)).sqrt().reciprocal()for a,b in combinations(allpoints,2));assert energy.lo>I(U).hi
 row={'triangle':data['name'],'point_rationals':[[str(x)for x in p]for p in points],'triangle_rationals':list(map(str,[u,v,t])),'pair_dot_max_exact':str(pairmax),'anchor_dot_max_upper':str(F(max(x.hi for r in ip for x in r),S)),'phi_each':[x.bounds()for x in phi],'phi_sum':total.bounds(),'budget':K.bounds(),'strict_auxiliary_margin':(K-total).bounds(),'nine_point_energy':energy.bounds(),'display_only':{'phi_sum':float(F(total.hi,S)),'budget':float(F(K.lo,S)),'auxiliary_margin':float(F(K.lo-total.hi,S)),'nine_point_energy':float(F(energy.lo,S)),'U':float(U)}};rows.append(row);print(data['name'],row['display_only'],flush=True)
out=BASE/'two_other_valleys2026_certified_witness.json';out.write_text(json.dumps({'status':'strict_counterexamples_to_six_phi_exclusion_only','bits':384,'not_thomson_counterexamples':True,'model_sha256':hashlib.sha256(modelpath.read_bytes()).hexdigest(),'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'rows':rows},indent=2)+'\n');print('SAVED',out)
