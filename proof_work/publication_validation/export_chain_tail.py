#!/usr/bin/env python3
"""Generate 807-term gathered bindings for all remaining single-axis chains (7..17 sources)."""
import json, math, sys
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parent
R = json.load(open(ROOT / 'independent_hermite_RH_result.json'))['R_coefficients']
D = json.load(open(ROOT / 'independent_local_00_AAA.json'))
Q = D['shifted_polynomial']; A = D['new_center_intervals']
LIMIT = int(sys.argv[1]) if len(sys.argv) > 1 else 0
src = [tuple(e) for e, _ in R]
Rint = {tuple(e): (F(v[0]), F(v[1])) for e, v in R}
Qint = {tuple(e): (F(v[0]), F(v[1])) for e, v in Q}
Aint = [(F(v[0]), F(v[1])) for v in A]

rows = []
for i, (e, _) in enumerate(R):
    k = tuple(e)
    ss = [x for x in src if all(x[j] >= k[j] for j in range(3))]
    m = len(ss)
    if not (7 <= m <= 17):
        continue
    axes = [j for j in range(3) if len({x[j] for x in ss}) > 1]
    if len(axes) != 1:
        continue
    ax = axes[0]
    if any(len({x[j] for x in ss}) != 1 for j in range(3) if j != ax):
        continue
    if sorted({x[ax] for x in ss}) != list(range(k[ax], k[ax] + m)):
        continue
    idx = [src.index(x) for x in ss]
    if idx != sorted(idx):
        raise SystemExit(f'non-manifest order {k} {idx}')
    rows.append((m, i, k, ss, ax, idx))
if LIMIT:
    rows = rows[:LIMIT]
print(f'tail chain rows: {len(rows)}')

def rat(x):
    f = F(x); return f'(({f.numerator} : ℚ) / {f.denominator})'

def idef(name, X):
    return f'def {name} : RatInterval := ⟨{rat(X[0])}, {rat(X[1])}, by rw [Rat.le_iff]; norm_num⟩'

def imul(X, Y):
    return (min(X[0]*Y[0], X[0]*Y[1], X[1]*Y[0], X[1]*Y[1]),
            max(X[0]*Y[0], X[0]*Y[1], X[1]*Y[0], X[1]*Y[1]))

def powI(X, n):
    z = (F(1), F(1))
    for _ in range(n):
        z = imul(z, X)
    return z

def vec(e):
    return '![' + ', '.join(str(x) for x in e) + ']'

out = ['import ThomsonNine.GatheredBinding',
       'import ThomsonNine.SparseTranslation\n',
       'set_option maxRecDepth 100000',
       'set_option maxHeartbeats 2000000\n',
       'open ThomsonNine',
       'open ThomsonNine.LocalSparseHessianAAA',
       'open ThomsonNine.Interval',
       'open ThomsonNine.Interval.RatInterval',
       'open ThomsonNine.Interval.SparsePolynomial\n',
       'namespace ThomsonNine.ChainTail\n']
audits = []
for m, i, k, ss, ax, idx in rows:
    tag = '_'.join(map(str, k))
    out.append(idef(f'Q_{tag}', Qint[k]))
    Rs = []
    for j, e in enumerate(ss):
        name = f'R{j}_{tag}'; Rs.append(name); out.append(idef(name, Rint[e]))
    Aname = f'A_{tag}'
    out.append(idef(Aname, Aint[ax]))
    Ks = []
    for j in range(1, m):
        n = math.comb(k[ax] + j, j)
        Kj = f'K{j}_{tag}'; Pw = f'Pw{j}_{tag}'
        Xp = powI(Aint[ax], j); Xk = imul(imul((F(n), F(n)), Rint[ss[j]]), Xp)
        out.append(idef(Pw, Xp)); out.append(idef(Kj, Xk)); Ks.append(Kj)
        out.append(f'''theorem {Pw}_mem (ha : {Aname}.mem a) :
    {Pw}.mem (a ^ {j}) := by
  refine mem_subset (powInterval_mem {Aname} a ha {j}) ?_ ?_
  · change {Pw}.lo ≤ (powInterval {Aname} {j}).lo
    simp only [powInterval, RatInterval.mul]
    norm_num [{Pw}, {Aname}]
  · change (powInterval {Aname} {j}).hi ≤ {Pw}.hi
    simp only [powInterval, RatInterval.mul]
    norm_num [{Pw}, {Aname}]

theorem {Kj}_mem (c{j} : ℝ) (h{j} : {Rs[j]}.mem c{j}) (ha : {Aname}.mem a) :
    {Kj}.mem (({n} * c{j}) * a ^ {j}) := by
  refine mem_subset (mem_mul (mem_mul (mem_const ({n} : ℚ)) h{j}) ({Pw}_mem ha)) ?_ ?_
  · change {Kj}.lo ≤ (mul (mul (const {n}) {Rs[j]}) {Pw}).lo
    rw [Rat.le_iff]; norm_num [{Kj}, {Rs[j]}, {Pw}]
  · change (mul (mul (const {n}) {Rs[j]}) {Pw}).hi ≤ {Kj}.hi
    rw [Rat.le_iff]; norm_num [{Kj}, {Rs[j]}, {Pw}]
''')
    factors = ['c0'] + [f'(({math.comb(k[ax]+j,j)} * c{j}) * a ^ {j})' for j in range(1, m)]
    sumexpr = factors[-1]
    for j in range(m - 2, 0, -1):
        sumexpr = f'({factors[j]} + {sumexpr})'
    sumexpr = f'({factors[0]} + {sumexpr})'
    isum = Rs[0]
    for j in range(1, m):
        isum = f'(add {isum} {Ks[j-1]})'
    hsum = 'h0'
    for j in range(1, m):
        hsum = f'(mem_add {hsum} hT{j})'
    hlo = Rs[0] + '.lo'
    for j in range(1, m):
        hlo = f'({hlo} + {Ks[j-1]}.lo)'
    hhi = Rs[0] + '.hi'
    for j in range(1, m):
        hhi = f'({hhi} + {Ks[j-1]}.hi)'
    cdecl = ' '.join(f'c{j}' for j in range(m))
    htypes = '\n    '.join(f'(h{j} : {Rs[j]}.mem c{j})' for j in range(m))
    hTlines = '\n'.join(f'  have hT{j} : {Ks[j-1]}.mem {factors[j]} := {Ks[j-1]}_mem c{j} h{j} ha' for j in range(1, m))
    nums = ', '.join(Ks)
    out.append(f'''theorem chain_target_{tag}_interval ({cdecl} : ℝ) {htypes}
    (ha : A_{tag}.mem a) :
    Q_{tag}.mem {sumexpr} := by
{hTlines}
  have hsum : {isum}.mem {sumexpr} := {hsum}
  refine mem_subset hsum ?_ ?_
  · change Q_{tag}.lo ≤ {hlo}
    rw [Rat.le_iff]; norm_num [Q_{tag}, {Rs[0]}, {nums}]
  · change {hhi} ≤ Q_{tag}.hi
    rw [Rat.le_iff]; norm_num [Q_{tag}, {Rs[0]}, {nums}]
''')
    hargs_g = '\n'.join(f'    (h{j} : {Rs[j]}.mem (c .t{idx[j]:03d}))' for j in range(m))
    hes = []
    for j in range(1, m):
        n = math.comb(k[ax] + j, j)
        coeff = f'(({n} * c .t{idx[j]:03d}) * a {ax} ^ {j})'
        if j == 1:
            proof = '    simp [expandedCoefficient, shiftFactor]\n    norm_num\n    ring'
        else:
            proof = f'''    simp [expandedCoefficient, shiftFactor]
    have hc : Nat.choose {ss[j][ax]} {k[ax]} = {n} := by decide
    rw [hc]
    ring_nf'''
        hes.append(f'''  have he{j} : expandedCoefficient (exponents .t{idx[j]:03d}) (exponents .t{i:03d}) (c .t{idx[j]:03d}) a = {coeff} := by
    have hk : exponents .t{i:03d} = {vec(k)} := rfl
    have h : exponents .t{idx[j]:03d} = {vec(ss[j])} := rfl
    rw [hk, h]
{proof}''')
    list_expr = '[' + ', '.join(f'.t{x:03d}' for x in idx) + ']'
    rewrites = 'he0' + ''.join(f', he{j}' for j in range(1, m))
    callargs = ' '.join(f'(c .t{x:03d})' for x in idx)
    hcall = ' '.join(f'h{j}' for j in range(m))
    out.append(f'''theorem t{i:03d}_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
{hargs_g}
    (ha : A_{tag}.mem (a {ax})) :
    (coefficientInterval .t{i:03d}).mem (ThomsonNine.GatheredBinding.gathered (exponents .t{i:03d}) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t{i:03d} i ≤ exponents t i)) = {list_expr} := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t{i:03d}) (exponents .t{i:03d}) (c .t{i:03d}) a = c .t{i:03d} := by
    have h : exponents .t{i:03d} = {vec(k)} := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
{chr(10).join(hes)}
  rw [{rewrites}]
  exact chain_target_{tag}_interval {callargs} (a := a {ax}) {hcall} ha
''')
    audits.append(f'#print axioms ThomsonNine.ChainTail.t{i:03d}_gathered_mem')
out.append('end ThomsonNine.ChainTail\n')
path = ROOT / 'formal/ThomsonNine/ChainTailBindings.lean'
path.write_text('\n'.join(out))
print(f'wrote {path} ({path.stat().st_size} bytes), {len(rows)} targets')
(ROOT / 'chain_tail_audits.txt').write_text('\n'.join(audits) + '\n')
