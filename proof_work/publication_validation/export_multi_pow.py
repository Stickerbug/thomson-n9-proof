import json,sys
from fractions import Fraction
from math import comb
from pathlib import Path
TARGET=sys.argv[1] if len(sys.argv)>1 else 't464'
FRAG=len(sys.argv)>2 and sys.argv[2]=='frag'
OUT=sys.argv[3] if len(sys.argv)>3 else '/home/dsh/Thomson Problem/proof_work/publication_validation/formal/ThomsonNine/MultiCornerPowTest.lean'
base=Path('/home/dsh/Thomson Problem/proof_work/publication_validation')
R=json.load(open(base/'independent_hermite_RH_result.json'))['R_coefficients']
J=json.load(open(base/'independent_local_00_AAA.json'))
QM={tuple(e):v for e,v in J['shifted_polynomial']}
A=[(Fraction(x[0]),Fraction(x[1])) for x in J['new_center_intervals']]
src=[tuple(e) for e,_ in R]
ki=int(TARGET[1:]); k=src[ki]
ss=[(j,x) for j,x in enumerate(src) if all(x[a]>=k[a] for a in range(3))]
assert len(ss)==5
srcnames=[f't{idx:03d}' for idx,_ in ss]
q=QM[k]; Q=(Fraction(q[0]),Fraction(q[1]))
def mul(I,J):
 v=[I[0]*J[0],I[0]*J[1],I[1]*J[0],I[1]*J[1]]; return (min(v),max(v))
def add(I,J): return (I[0]+J[0],I[1]+J[1])
def rat(x): return f'({x.numerator} / {x.denominator} : ℚ)'
def idef(name,I):
 pr='by rw [Rat.le_iff]' if I[0]==I[1] else 'by rw [Rat.le_iff]; norm_num'
 return f'def {name} : RatInterval := ⟨{rat(I[0])}, {rat(I[1])}, {pr}⟩\n'
def corners(K,I,J,h1,h2,ind='  '):
 return (f'{ind}refine mem_mul_of_bounds {h1} {h2} ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>\n'
         f'{ind}  (simp only [{K}, {I}, {J}, A0, A1, A2, RatInterval.const]; rw [Rat.le_iff]; norm_num)\n')
L=[]
if not FRAG:
    L.append('''import ThomsonNine.LocalSparseHessianAAABase
import ThomsonNine.SparseTranslation
import ThomsonNine.IntervalSum
import ThomsonNine.GatheredBinding

noncomputable section
namespace ThomsonNine.MultiCornerPow

open ThomsonNine
open ThomsonNine.Interval
open ThomsonNine.Interval.RatInterval
open ThomsonNine.LocalSparseHessianAAA
open ThomsonNine.Interval.SparsePolynomial
open ThomsonNine.GatheredBinding

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

''')
else:
    L.append(f'-- {TARGET}\n')
if not FRAG:
 for i in range(3): L.append(idef(f'A{i}',A[i]))
L.append(idef(f'Q_{TARGET}',Q))
for j,(idx,e) in enumerate(ss): L.append(idef(f'R{j}_{TARGET}',(Fraction(R[idx][1][0]),Fraction(R[idx][1][1]))))
S={}  # (j,ax) -> dict(final, expr, defs list [(name,val,alias)], proof info)
for j,(idx,e) in enumerate(ss):
 for ax in range(3):
  d=e[ax]-k[ax]; ch=comb(e[ax],k[ax]); final=f'S{j}_{ax}_{TARGET}'; levels=[]; expr=None
  if d==0:
   L.append(idef(final,(Fraction(ch),Fraction(ch))))
   S[(j,ax)]={'final':final,'expr':f'({ch})','kind':'const','ch':ch,'levels':[],'d':0}
  elif ch==1:
   p1=f'S{j}_{ax}_1_{TARGET}'
   L.append(f'def {p1} : RatInterval := A{ax}\n')
   levels.append((p1,None))
   prev_expr=f'(a {ax})'
   for t in range(2,d+1):
    pn=f'S{j}_{ax}_{t}_{TARGET}'
    L.append(idef(pn,mul((A[ax]),A[ax]) if t==2 else mul(S[(j,ax)]['levels'][-1][1],A[ax])))  # placeholder fixed below
    levels.append((pn,None))
   # compute intervals separately
   cur=A[ax]
   for i,(pn,_) in enumerate(levels):
    if i==0: cur=A[ax]
    else:
     cur=mul(cur,A[ax]); L.append(idef(pn,cur))  # duplicate for i>0; first already alias
   L.append(f'def {final} : RatInterval := {levels[-1][0]}\n')
   ee=prev_expr
   for t in range(2,d+1): ee=f'({ee} * a {ax})'
   S[(j,ax)]={'final':final,'expr':ee,'kind':'one','ch':1,'levels':levels,'d':d}
  else:
   # const ch then multiply A d times
   p0=f'S{j}_{ax}_0_{TARGET}'
   L.append(idef(p0,(Fraction(ch),Fraction(ch))))
   levels=[(p0,(Fraction(ch),Fraction(ch)))]
   cur=(Fraction(ch),Fraction(ch)); ee=f'({ch})'
   for t in range(1,d+1):
    pn=f'S{j}_{ax}_{t}_{TARGET}'
    cur=mul(cur,A[ax]); L.append(idef(pn,cur)); levels.append((pn,cur))
    ee=f'({ee} * a {ax})'
   L.append(f'def {final} : RatInterval := {levels[-1][0]}\n')
   S[(j,ax)]={'final':final,'expr':ee,'kind':'multi','ch':ch,'levels':levels,'d':d}
# C intervals
Cvals={}
for j,(idx,e) in enumerate(ss):
 prev=(Fraction(R[idx][1][0]),Fraction(R[idx][1][1]))
 for ax in range(3):
  prev=mul(prev,S[(j,ax)]['levels'][-1][1] if S[(j,ax)]['d']>0 else (Fraction(S[(j,ax)]['ch']),Fraction(S[(j,ax)]['ch'])))
  Cvals[(j,ax)]=prev
  L.append(idef(f'C{j}_{ax}_{TARGET}',prev))
Ksum=Cvals[(0,2)]
for j in range(1,5): Ksum=add(Ksum,Cvals[(j,2)])
L.append(f'def Ksum_{TARGET} : RatInterval := C0_2_{TARGET}.add (C1_2_{TARGET}.add (C2_2_{TARGET}.add (C3_2_{TARGET}.add C4_2_{TARGET})))\n\n')
args=[f'(c{j} : ℝ)' for j in range(5)]; hyps=[f'(h{j} : R{j}_{TARGET}.mem c{j})' for j in range(5)]
for ax in range(3): hyps.append(f'(ha{ax} : A{ax}.mem (a {ax}))')
sig=' '.join(args+['(a : Fin 3 → ℝ)']+hyps)
parts=[f'expandedCoefficient (exponents .{srcnames[j]}) (exponents .{TARGET}) c{j} a' for j in range(5)]
sexpr=f'({parts[0]} + ({parts[1]} + ({parts[2]} + ({parts[3]} + {parts[4]}))))'
L.append(f'theorem {TARGET}_sum {sig} :\n    Q_{TARGET}.mem ({sexpr}) := by\n')
for j,(idx,e) in enumerate(ss):
 hs=[]
 for ax in range(3):
  info=S[(j,ax)]; d=info['d']; ch=info['ch']; final=info['final']; levels=info['levels']
  if d==0:
   L.append(f'  have h{final} : {final}.mem ({ch} : ℝ) := by\n    constructor <;> simp [{final}]\n')
  elif info['kind']=='one':
   p1=levels[0][0]
   L.append(f'  have h{p1} : {p1}.mem (a {ax}) := by\n    simpa [{p1}] using ha{ax}\n')
   for t in range(2,d+1):
    pn=levels[t-1][0]; pm=levels[t-2][0]
    L.append(f'  have h{pn} : {pn}.mem ({info["expr"] if t==d else "("+ " * ".join(["a "+str(ax)]*t) +")"}) := by\n')
    L.append(corners(pn,pm,f'A{ax}',f'h{pm}',f'ha{ax}','    '))
   if d>=2:
    L.append(f'  have h{final} : {final}.mem {info["expr"]} := by\n    simpa [{final}] using h{levels[-1][0]}\n')
  else:
   p0=levels[0][0]
   L.append(f'  have h{p0} : {p0}.mem ({ch} : ℝ) := by\n    constructor <;> simp [{p0}]\n')
   ee=f'({ch})'
   for t in range(1,d+1):
    pn=levels[t][0]; pm=levels[t-1][0]
    ee=f'({ee} * a {ax})'
    L.append(f'  have h{pn} : {pn}.mem {ee} := by\n')
    L.append(corners(pn,pm,f'A{ax}',f'h{pm}',f'ha{ax}','    '))
   L.append(f'  have h{final} : {final}.mem {info["expr"]} := by\n    simpa [{final}] using h{levels[-1][0]}\n')
  hs.append(f'h{final}')
 prev_h=f'h{j}'; prev_name=f'R{j}_{TARGET}'; expr=f'c{j}'
 for ax in range(3):
  expr=f'({expr} * {S[(j,ax)]["expr"]})'
  cn=f'C{j}_{ax}_{TARGET}'
  L.append(f'  have h{cn} : {cn}.mem {expr} := by\n')
  L.append(corners(cn,prev_name,', '.join([S[(j,ax)]['final']]+[nm for nm,_ in S[(j,ax)]['levels']]),prev_h,f'h{S[(j,ax)]["final"]}','    '))
  prev_h=f'h{cn}'; prev_name=cn
 c2=f'C{j}_2_{TARGET}'
 L.append(f'  have hK{j} : {c2}.mem (expandedCoefficient (exponents .{srcnames[j]}) (exponents .{TARGET}) c{j} a) := by\n')
 evec='!['+', '.join(str(x) for x in ss[j][1])+']'; kvec='!['+', '.join(str(x) for x in k)+']'
 L.append(f'    rw [show exponents .{srcnames[j]} = {evec} from rfl]\n')
 L.append(f'    try rw [show exponents .{TARGET} = {kvec} from rfl]\n')
 dmax=max(e[a]-k[a] for a in range(3))
 proof=('by simp [expandedCoefficient, shiftFactor]' if dmax<=1 else 'by unfold expandedCoefficient shiftFactor; norm_num [Nat.choose]; try ring; try simp')
 L.append(f'    rw [show expandedCoefficient {evec} {kvec} c{j} a = {expr} from {proof}]\n')
 L.append(f'    exact h{c2}\n')
L.append(f'  have hsum : Ksum_{TARGET}.mem ({sexpr}) := by\n')
L.append(f'    simpa [Ksum_{TARGET}] using mem_add hK0 (mem_add hK1 (mem_add hK2 (mem_add hK3 hK4)))\n')
L.append('  refine mem_subset hsum ?_ ?_\n')
for lo,op in [('lo','≤'),('hi','≤')]:
 if lo=='lo':
  L.append(f'  · change Q_{TARGET}.lo ≤ Ksum_{TARGET}.lo\n')
 else:
  L.append(f'  · change Ksum_{TARGET}.hi ≤ Q_{TARGET}.hi\n')
 L.append(f'    unfold Q_{TARGET} Ksum_{TARGET} C0_2_{TARGET} C1_2_{TARGET} C2_2_{TARGET} C3_2_{TARGET} C4_2_{TARGET}\n')
 L.append('    rw [Rat.le_iff]; norm_num [RatInterval.add]\n')
gl='[' + ', '.join(f'.{x}' for x in srcnames) + ']'
args2=' '.join([f'(h{j} : R{j}_{TARGET}.mem (c .{srcnames[j]}))' for j in range(5)])+' (ha0 : A0.mem (a 0)) (ha1 : A1.mem (a 1)) (ha2 : A2.mem (a 2))'
L.append(f'theorem {TARGET}_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ) {args2} :\n    (coefficientInterval .{TARGET}).mem (gathered (exponents .{TARGET}) c a) := by\n')
L.append(f'  have hQ : coefficientInterval .{TARGET} = Q_{TARGET} := by rfl\n  rw [hQ]\n')
L.append(f'  have hf : allTerms.filter (fun t => decide (∀ i, (exponents .{TARGET}) i ≤ exponents t i)) = {gl} := by rfl\n  rw [gathered, hf]\n')
L.append('  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]\n')
call=' '.join([f'(c .{srcnames[j]})' for j in range(5)])+' a '+' '.join([f'h{j}' for j in range(5)])+' ha0 ha1 ha2'
L.append(f'  exact {TARGET}_sum {call}\n\n')
if not FRAG: L.append('end MultiCornerPow\n')
out=''.join(L)
Path(OUT).write_text(out)
print('wrote',len(out))
