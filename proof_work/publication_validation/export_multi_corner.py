import json
from fractions import Fraction
from math import comb
from pathlib import Path
base=Path('/home/dsh/Thomson Problem/proof_work/publication_validation')
R=json.load(open(base/'independent_hermite_RH_result.json'))['R_coefficients']
J=json.load(open(base/'independent_local_00_AAA.json'))
QM={tuple(e):v for e,v in J['shifted_polynomial']}
A=[(Fraction(x[0]),Fraction(x[1])) for x in J['new_center_intervals']]
src=[tuple(e) for e,_ in R]

def mul(I,J):
    v=[I[0]*J[0],I[0]*J[1],I[1]*J[0],I[1]*J[1]]
    return (min(v),max(v))
def add(I,J): return (I[0]+J[0],I[1]+J[1])
def rat(x): return f'({x.numerator} / {x.denominator} : ℚ)'
def idef(name,I):
    pr='by rw [Rat.le_iff]' if I[0]==I[1] else 'by rw [Rat.le_iff]; norm_num'
    return f'def {name} : RatInterval := ⟨{rat(I[0])}, {rat(I[1])}, {pr}⟩\n'
def corners(K,I,J,h1,h2,indent='  '):
    return (f'{indent}refine mem_mul_of_bounds {h1} {h2} ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>\n'
            f'{indent}  (simp only [{K}, {I}, {J}, A0, A1, A2, RatInterval.const]; rw [Rat.le_iff]; norm_num)\n')

TARGETS=['t125','t244','t330','t404','t470','t532','t538','t591','t608','t648','t672','t699','t726','t740','t766']
L=['''import ThomsonNine.LocalSparseHessianAAABase
import ThomsonNine.SparseTranslation
import ThomsonNine.IntervalSum
import ThomsonNine.GatheredBinding

noncomputable section
namespace ThomsonNine.MultiCorner

open ThomsonNine
open ThomsonNine.Interval
open ThomsonNine.Interval.RatInterval
open ThomsonNine.LocalSparseHessianAAA
open ThomsonNine.Interval.SparsePolynomial
open ThomsonNine.GatheredBinding

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

''']
for i in range(3): L.append(idef(f'A{i}',A[i]))
L.append('\n')
for TARGET in TARGETS:
    ki=int(TARGET[1:]); k=src[ki]
    ss=[(j,x) for j,x in enumerate(src) if all(x[a]>=k[a] for a in range(3))]
    assert len(ss)==5, (TARGET,len(ss))
    srcnames=[f't{idx:03d}' for idx,_ in ss]
    q=QM[k]; Q=(Fraction(q[0]),Fraction(q[1]))
    L.append(f'-- {TARGET}\n')
    L.append(idef(f'Q_{TARGET}',Q))
    for j,(idx,e) in enumerate(ss):
        L.append(idef(f'R{j}_{TARGET}',(Fraction(R[idx][1][0]),Fraction(R[idx][1][1]))))
    S={}; Cvals={}
    for j,(idx,e) in enumerate(ss):
        for ax in range(3):
            d=e[ax]-k[ax]; ch=comb(e[ax],k[ax])
            val=(Fraction(ch),Fraction(ch)) if d==0 else (A[ax] if ch==1 else mul((Fraction(ch),Fraction(ch)),A[ax]))
            S[(j,ax)]=(ch,d,val)
            if d==0 or ch!=1: L.append(idef(f'S{j}_{ax}_{TARGET}',val))
            else: L.append(f'def S{j}_{ax}_{TARGET} : RatInterval := A{ax}\n')
        prev=(Fraction(R[idx][1][0]),Fraction(R[idx][1][1]))
        for ax in range(3):
            prev=mul(prev,S[(j,ax)][2]); Cvals[(j,ax)]=prev
            L.append(idef(f'C{j}_{ax}_{TARGET}',prev))
    Ksum=Cvals[(0,2)]
    for j in range(1,5): Ksum=add(Ksum,Cvals[(j,2)])
    L.append(f'def Ksum_{TARGET} : RatInterval := C0_2_{TARGET}.add (C1_2_{TARGET}.add (C2_2_{TARGET}.add (C3_2_{TARGET}.add C4_2_{TARGET})))\n\n')
    args=[f'(c{j} : ℝ)' for j in range(5)]
    hyps=[f'(h{j} : R{j}_{TARGET}.mem c{j})' for j in range(5)]
    for ax in range(3): hyps.append(f'(ha{ax} : A{ax}.mem (a {ax}))')
    sig=' '.join(args+['(a : Fin 3 → ℝ)']+hyps)
    parts_sig=[f'expandedCoefficient (exponents .{srcnames[j]}) (exponents .{TARGET}) c{j} a' for j in range(5)]
    sexpr_sig=f'({parts_sig[0]} + ({parts_sig[1]} + ({parts_sig[2]} + ({parts_sig[3]} + {parts_sig[4]}))))'
    L.append(f'theorem {TARGET}_sum {sig} :\n    Q_{TARGET}.mem ({sexpr_sig}) := by\n')
    for j,(idx,e) in enumerate(ss):
        hs=[]
        for ax in range(3):
            ch,d,I=S[(j,ax)]; sn=f'S{j}_{ax}_{TARGET}'
            if d==0:
                L.append(f'  have h{sn} : {sn}.mem ({ch} : ℝ) := by\n    constructor <;> simp [{sn}]\n')
            elif ch==1:
                L.append(f'  have h{sn} : {sn}.mem ({ch} * a {ax}) := by\n    simpa [{sn}] using ha{ax}\n')
            else:
                L.append(f'  have h{sn} : {sn}.mem ({ch} * a {ax}) := by\n')
                L.append(corners(sn,'RatInterval.const',f'A{ax}',f'(mem_const ({ch} : ℚ))',f'(ha{ax})','    '))
            hs.append(f'h{sn}')
        prev_h=f'h{j}'; prev_name=f'R{j}_{TARGET}'
        expr=f'c{j}'; sfs=[]
        for ax in range(3):
            ch,d,_=S[(j,ax)]; sfs.append(f'({ch})' if d==0 else f'({ch} * a {ax})')
        for ax in range(3):
            expr=f'({expr} * {sfs[ax]})'
            cn=f'C{j}_{ax}_{TARGET}'
            L.append(f'  have h{cn} : {cn}.mem {expr} := by\n')
            L.append(corners(cn,prev_name,f'S{j}_{ax}_{TARGET}',prev_h,f'hS{j}_{ax}_{TARGET}','    '))
            prev_h=f'h{cn}'; prev_name=cn
        c2=f'C{j}_2_{TARGET}'
        L.append(f'  have hK{j} : {c2}.mem (expandedCoefficient (exponents .{srcnames[j]}) (exponents .{TARGET}) c{j} a) := by\n')
        evec='!['+', '.join(str(x) for x in ss[j][1])+']'; kvec='!['+', '.join(str(x) for x in k)+']'
        L.append(f'    rw [show exponents .{srcnames[j]} = {evec} from rfl]\n')
        L.append(f'    try rw [show exponents .{TARGET} = {kvec} from rfl]\n')
        L.append(f'    rw [show expandedCoefficient {evec} {kvec} c{j} a = {expr} from by simp [expandedCoefficient, shiftFactor]]\n')
        L.append(f'    exact h{c2}\n')
    parts=[f'expandedCoefficient (exponents .{srcnames[j]}) (exponents .{TARGET}) c{j} a' for j in range(5)]
    sexpr=f'({parts[0]} + ({parts[1]} + ({parts[2]} + ({parts[3]} + {parts[4]}))))'
    L.append(f'  have hsum : Ksum_{TARGET}.mem ({sexpr}) := by\n')
    L.append(f'    simpa [Ksum_{TARGET}] using mem_add hK0 (mem_add hK1 (mem_add hK2 (mem_add hK3 hK4)))\n')
    L.append('  refine mem_subset hsum ?_ ?_\n')
    L.append(f'  · change Q_{TARGET}.lo ≤ Ksum_{TARGET}.lo\n')
    L.append(f'    unfold Q_{TARGET} Ksum_{TARGET} C0_2_{TARGET} C1_2_{TARGET} C2_2_{TARGET} C3_2_{TARGET} C4_2_{TARGET}\n')
    L.append('    rw [Rat.le_iff]; norm_num [RatInterval.add]\n')
    L.append(f'  · change Ksum_{TARGET}.hi ≤ Q_{TARGET}.hi\n')
    L.append(f'    unfold Q_{TARGET} Ksum_{TARGET} C0_2_{TARGET} C1_2_{TARGET} C2_2_{TARGET} C3_2_{TARGET} C4_2_{TARGET}\n')
    L.append('    rw [Rat.le_iff]; norm_num [RatInterval.add]\n')
    gl='[' + ', '.join(f'.{x}' for x in srcnames) + ']'
    args2=' '.join([f'(h{j} : R{j}_{TARGET}.mem (c .{srcnames[j]}))' for j in range(5)])
    args2 += ' (ha0 : A0.mem (a 0)) (ha1 : A1.mem (a 1)) (ha2 : A2.mem (a 2))'
    L.append(f'theorem {TARGET}_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ) {args2} :\n')
    L.append(f'    (coefficientInterval .{TARGET}).mem (gathered (exponents .{TARGET}) c a) := by\n')
    L.append(f'  have hQ : coefficientInterval .{TARGET} = Q_{TARGET} := by rfl\n')
    L.append('  rw [hQ]\n')
    L.append(f'  have hf : allTerms.filter (fun t => decide (∀ i, (exponents .{TARGET}) i ≤ exponents t i)) = {gl} := by rfl\n')
    L.append('  rw [gathered, hf]\n')
    L.append('  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]\n')
    call=' '.join([f'(c .{srcnames[j]})' for j in range(5)]) + ' a ' + ' '.join([f'h{j}' for j in range(5)]) + ' ha0 ha1 ha2'
    L.append(f'  exact {TARGET}_sum {call}\n\n')
L.append('end MultiCorner\n')
out=''.join(L)
Path('/home/dsh/Thomson Problem/proof_work/publication_validation/formal/ThomsonNine/MultiCornerBindings.lean').write_text(out)
print('wrote',len(out))
