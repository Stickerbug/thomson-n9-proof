import json,sys
from fractions import Fraction as F
from math import comb
P='/home/dsh/Thomson Problem/proof_work/publication_validation/'
R=json.load(open(P+'independent_hermite_RH_result.json'))['R_coefficients']
J=json.load(open(P+'independent_local_00_AAA.json'))
QM={tuple(e):v for e,v in J['shifted_polynomial']}; A=[(F(x[0]),F(x[1])) for x in J['new_center_intervals']]
IDX=int(sys.argv[1]); OUT=sys.argv[2]; NS=sys.argv[3]
K=tuple(R[IDX][0]); TARGET=f't{IDX:03d}'; Q=tuple(map(F,QM[K]))
src=[(i,tuple(x[0]),(F(x[1][0]),F(x[1][1]))) for i,x in enumerate(R) if all(x[0][j]>=K[j] for j in range(3))]
M=len(src)
assert M>=2
def rat(q): return f'({q.numerator} / {q.denominator} : ℚ)'
def idef(n,I):
 pr='by rw [Rat.le_iff]' if I[0]==I[1] else 'by rw [Rat.le_iff]; norm_num'
 return f'private def {n} : RatInterval := ⟨{rat(I[0])}, {rat(I[1])}, {pr}⟩\n'
L=[]; defs=[]
L.append(f'''import ThomsonNine.LocalSparseHessianAAABase
import ThomsonNine.SparseTranslation
import ThomsonNine.IntervalSum
import ThomsonNine.GatheredBinding
noncomputable section
namespace ThomsonNine.{NS}
open ThomsonNine
open ThomsonNine.Interval
open ThomsonNine.Interval.RatInterval
open ThomsonNine.LocalSparseHessianAAA
open ThomsonNine.Interval.SparsePolynomial
open ThomsonNine.GatheredBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
''')
for i in range(3): n=f'A{i}'; L.append(idef(n,A[i])); defs.append(n)
L.append(idef('Q_'+TARGET,Q)); defs.append('Q_'+TARGET)
for j,(_,e,I) in enumerate(src): n=f'R{j}_{TARGET}'; L.append(idef(n,I)); defs.append(n)
S={}
for ax in range(3):
 for val in sorted({e[ax] for _,e,_ in src}):
  d=val-K[ax]
  if d==0: continue
  ch=comb(val,K[ax]); base=f'Sb{ax}_{val}_{TARGET}'; L.append(idef(base,(F(ch),F(ch)))); defs.append(base)
  prev=base
  for t in range(1,d+1):
   nm=f'S{ax}_{val}_{t}_{TARGET}'; L.append(f'private def {nm} : RatInterval := {prev}.mul A{ax}\n'); defs.append(nm); prev=nm
  S[(ax,val)]=prev
cur=[{'e':list(e),'expr':f'c{j}','idef':f'R{j}_{TARGET}','name':f'q{j}','hname':f'h{j}','members':[j],'parent':None,'parent_h':None,'items':None} for j,(_,e,_) in enumerate(src)]
stages=[]
for ax in range(3):
 trans=[]
 for it in cur:
  val=it['e'][ax]; d=val-K[ax]
  if d==0: trans.append(dict(it)); continue
  ch=comb(val,K[ax]); sn=S[(ax,val)]
  sfexpr=f'{ch} * a {ax}' if d==1 else '('+ ' * '.join([str(ch)]+[f'a {ax}']*d)+')'
  tn=f'T{ax}_{len(trans)}_{TARGET}'
  L.append(f'private def {tn} : RatInterval := {it["idef"]}.mul {sn}\n'); defs.append(tn)
  trans.append({'e':list(it['e']),'expr':f'({it["expr"]}) * ({sfexpr})','idef':tn,'name':tn,'hname':f'h{tn}','members':it['members'],'parent':it['name'],'parent_h':it['hname'],'items':None})
 groups={}
 for it in trans:
  ne=list(it['e']); ne[ax]=K[ax]; groups.setdefault(tuple(ne),[]).append(it)
 new=[]
 for key,items in sorted(groups.items()):
  if len(items)==1: new.append(dict(items[0],e=list(key)))
  else:
   gn=f'G{ax}_{len(new)}_{TARGET}'
   expr=items[-1]['expr']
   for it in reversed(items[:-1]): expr=f'{it["expr"]} + ({expr})'
   de=items[-1]['idef']
   for it in reversed(items[:-1]): de=f'{it["idef"]}.add ({de})'
   L.append(f'private def {gn} : RatInterval := {de}\n'); defs.append(gn)
   new.append({'e':list(key),'expr':expr,'idef':gn,'name':gn,'hname':f'h{gn}','members':[m for it in items for m in it['members']],'parent':None,'parent_h':None,'items':items})
 stages.append((ax,trans,groups,new)); cur=new
FINAL=cur[0]['expr']; finalname=cur[0]['name']
ghyps=' '.join([f'(h{j} : R{j}_{TARGET}.mem (c .t{src[j][0]:03d}))' for j in range(M)]+[f'(ha{i} : A{i}.mem (a {i}))' for i in range(3)])
import re as _re
FINAL_C=_re.sub(r'c([0-9]+)', lambda m:f'(c .t{src[int(m.group(1))][0]:03d})', FINAL)
args=' '.join(f'c{j}' for j in range(M))+' : ℝ) (a : Fin 3 → ℝ'
hyps=' '.join([f'(h{j} : R{j}_{TARGET}.mem c{j})' for j in range(M)]+[f'(ha{i} : A{i}.mem (a {i}))' for i in range(3)])
L.append(f'''theorem {TARGET}_sum ({args})
  {hyps} :
  Q_{TARGET}.mem ({FINAL}) := by
''')
# hS proofs
for ax in range(3):
 for val in sorted({e[ax] for _,e,_ in src}):
  d=val-K[ax]
  if d==0: continue
  ch=comb(val,K[ax]); base=f'Sb{ax}_{val}_{TARGET}'
  L.append(f'  have h{base} : {base}.mem ({ch} : ℝ) := by constructor <;> simp [{base}]\n')
  prev=base; pexpr=f'{ch}'
  for t in range(1,d+1):
   nm=f'S{ax}_{val}_{t}_{TARGET}'
   L.append(f'''  have h{nm} : {nm}.mem ({pexpr} * a {ax}) := by
    refine mem_mul_of_bounds h{prev} ha{ax} ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (simp only [{nm}, {prev}, {", ".join(defs)}, RatInterval.const]; rw [Rat.le_iff]; norm_num [RatInterval.add, RatInterval.mul])
''')
   prev=nm; pexpr=f'({pexpr} * a {ax})'
# stage proofs
for ax,trans,groups,new in stages:
 for it in trans:
  if it['parent'] is None: continue
  sn=S[(ax,it['e'][ax])]
  L.append(f'''  have h{it["name"]} : {it["name"]}.mem ({it["expr"]}) := by
    refine mem_mul_of_bounds {it["parent_h"]} h{sn} ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (simp only [{it["name"]}, {", ".join(defs)}, RatInterval.const]; rw [Rat.le_iff]; norm_num [RatInterval.add, RatInterval.mul])
''')
 for key,items in sorted(groups.items()):
  ni=[x for x in new if tuple(x['e'])==key][0]
  if len(items)==1: continue
  inner=items[-1]['hname']
  for it in reversed(items[:-1]): inner=f'mem_add {it["hname"]} ({inner})'
  L.append(f'  have h{ni["name"]} : {ni["name"]}.mem ({ni["expr"]}) := by simpa [{ni["name"]}, add_assoc] using {inner}\n')
L.append(f'''  refine mem_subset {cur[0]['hname']} ?_ ?_
  · simp only [{", ".join(defs)}, RatInterval.const]
    rw [Rat.le_iff]; norm_num [RatInterval.add, RatInterval.mul]
  · simp only [{", ".join(defs)}, RatInterval.const]
    rw [Rat.le_iff]; norm_num [RatInterval.add, RatInterval.mul]

theorem {TARGET}_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
  {ghyps} :
  (coefficientInterval .{TARGET}).mem (gathered (exponents .{TARGET}) c a) := by
  have hf : allTerms.filter (fun t => decide (∀ i, (exponents .{TARGET}) i ≤ exponents t i)) = [{", ".join(f'.t{src[j][0]:03d}' for j in range(M))}] := by rfl
  rw [gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have hQ : coefficientInterval .{TARGET} = Q_{TARGET} := by rfl
  rw [hQ]
  have heq : (''')
# heq sum expression
terms=[f'expandedCoefficient (exponents .t{src[j][0]:03d}) (exponents .{TARGET}) (c .t{src[j][0]:03d}) a' for j in range(M)]
expr=terms[-1]
for t in reversed(terms[:-1]): expr=f'{t} + ({expr})'
L.append(expr+f''') = {FINAL_C} := by
    simp [expandedCoefficient, shiftFactor, Nat.choose, exponents]
    ring
  rw [heq]
  exact {TARGET}_sum {" ".join(f'(c .t{src[j][0]:03d})' for j in range(M))} a {" ".join(f'h{j}' for j in range(M))} ha0 ha1 ha2
end {NS}
''')
open(OUT,'w').write(''.join(L)); print('wrote',OUT,len(''.join(L)))
