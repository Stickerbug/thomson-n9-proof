"""Exact classification of all 84 candidate triangles, as polynomials in r."""
from itertools import combinations
from collections import Counter
from pathlib import Path
from fractions import Fraction as F
import sympy as s
import json
from certify_all_degree import I,S,L,U,derivative
r=s.symbols('r');values={'A':1-s.Rational(3,2)*r*r,'B':2*r*r-1,'C':r*r/2-1,'D':-s.Rational(1,2),'F':r/2,'G':-r}
def label(i,j):
 if i==j:return 'diagonal'
 if i<6 and j<6:
  if i%3==j%3:return 'B'
  return 'A' if i//3==j//3 else 'C'
 if i>=6 and j>=6:return 'D'
 if j<6:i,j=j,i
 delta=(2*(i%3)-(2*(j-6)+1))%6
 assert delta in (1,3,5)
 return 'G' if delta==3 else 'F'
pairs=Counter(label(i,j)for i,j in combinations(range(9),2))
assert pairs=={'A':6,'B':3,'C':6,'D':3,'F':12,'G':6}
counts=Counter(tuple(sorted((label(i,j),label(i,k),label(j,k))))for i,j,k in combinations(range(9),3))
assert len(counts)==12 and sum(counts.values())==84
rr=I(L,U);assert derivative(I(L)).hi<0<derivative(I(U)).lo
rows=[];boundary=[]
for labels,n in sorted(counts.items()):
 u,v,t=(values[z]for z in labels);gram=s.Poly(1+2*u*v*t-u*u-v*v-t*t,r)
 if gram.is_zero:
  boundary.append(labels);status='identically_boundary';bounds=None
 else:
  g=I(0)
  for q in gram.all_coeffs():g=g*rr+F(int(s.numer(q)),int(s.denom(q)))
  assert g.lo>0,(labels,g.bounds());status='certified_interior_at_true_root';bounds=g.bounds()
 rows.append({'labels':list(labels),'multiplicity':n,'inner_products':[str(values[z])for z in labels],'Gram_factorization':str(s.factor(gram.as_expr())),'status':status,'Gram_interval':bounds})
assert set(boundary)=={('C','F','F'),('B','G','G'),('D','D','D')}
out={'status':'exact_candidate_classification','pair_multiplicities':dict(sorted(pairs.items())),'triangle_total':84,'triangle_types':rows,'scope':'Necessary candidate contact locations, not a proof of global optimality. Polynomials are exact in the true stationary parameter r_star; interval bracket only certifies which triangles are interior.'}
p=Path(__file__).with_name('candidate_triple_types_v1.json')
if p.exists():assert json.loads(p.read_text())==out
else:p.write_text(json.dumps(out,indent=2)+'\n')
print('PASS 36 pairs,84 triples,12 types,exactly three boundary types at true r_star.')
for row in rows:print(row['labels'],row['multiplicity'],row['Gram_factorization'],row['status'])
