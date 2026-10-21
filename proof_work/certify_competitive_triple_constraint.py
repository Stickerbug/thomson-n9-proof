"""Necessary polynomial triple condition from the global two-point defect budget."""
from certify_rational_lp import F,add,scale,mul
from certify_conditional_h19 import check
from pathlib import Path
import json
base=Path(__file__).parent
a=list(map(F,json.loads((base/'rational_lp24.json').read_text())['legendre_coefficients']));P=[[F(1)],[F(0),F(1)]]
for k in range(2,len(a)):P.append(scale(add(scale([F(0)]+P[-1],2*k-1),scale(P[-2],1-k)),F(1,k)))
p=[F(0)]
for v,poly in zip(a,P):p=add(p,scale(poly,v))
h=list(map(F,json.loads((base/'conditional_h19_certificate.json').read_text())['h_monomial']));defect=add(h,scale(p,-1))
B=36*a[0]-F(9,2)*sum(a[1:]);U=F('25.75998653126983156407570227376049402866');gap=U-B
C={(0,0,0):gap}
for axis in range(3):
 for k,v in enumerate(defect):
  e=[0,0,0];e[axis]=k;e=tuple(e);C[e]=C.get(e,F(0))-v
C={e:v for e,v in C.items()if v};corner=sum(v*F(14,25)**sum(e)for e,v in C.items());assert corner<0
# Every pair in [.5,.56] individually has polynomial defect >gap/3.
leafnodes=check(add(defect,[-gap/3]),F(1,2),F(14,25))
result={'status':'certified_necessary_condition','claim':'For any competitive nine-point configuration, every triple has C(u,v,t)>=0. No triple can have all three inner products >=1/2.','domain':['-1','14/25'],'gap':str(gap),'C_monomial':[[list(e),str(v)]for e,v in C.items()],'corner_value_exact':str(corner),'no_close_triangle_univariate_nodes':leafnodes,'logic':'E-B=sum36(f-p)+positive moments <=U-B. Every triple sum(f-p)<=gap, while h<=f gives sum(h-p)<=gap. Univariate h-p>gap/3 on [.5,.56] excludes triples entirely in that interval.'}
q=base/'competitive_triple_constraint_certificate.json';assert not q.exists();q.write_text(json.dumps(result,indent=2)+'\n');print('PASS necessary triple polynomial, corner negative, no >=.5 triangle;',leafnodes,'Bernstein nodes',flush=True)
