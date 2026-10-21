#!/usr/bin/env python3
"""Generate Lean interval bindings for all archived two-source targets except .t126."""
import json
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parent
R = json.load(open(ROOT / 'independent_hermite_RH_result.json'))['R_coefficients']
Q = json.load(open(ROOT / 'independent_local_00_AAA.json'))['shifted_polynomial']
A = json.load(open(ROOT / 'independent_local_00_AAA.json'))['new_center_intervals']

def rat(x):
    f = F(x); n, d = f.numerator, f.denominator
    return f'(({n} : ℚ) / {d})'

def interval(name, lo, hi, comment=''):
    return (f'def {name} : RatInterval := ⟨{rat(lo)}, {rat(hi)}, by rw [Rat.le_iff]; norm_num⟩' + (f' -- {comment}' if comment else ''))

def mul(X, Y):
    lo = min(X[0]*Y[0], X[0]*Y[1], X[1]*Y[0], X[1]*Y[1]); hi = max(X[0]*Y[0], X[0]*Y[1], X[1]*Y[0], X[1]*Y[1]); return (lo, hi)

def add(X, Y): return (X[0]+Y[0], X[1]+Y[1])

src = [tuple(e) for e, _ in R]
q = {tuple(e): (F(v[0]), F(v[1])) for e, v in Q}
Rint = {tuple(e): (F(v[0]), F(v[1])) for e, v in R}

rows = []
for i, (e, iv) in enumerate(R):
    k = tuple(e)
    cand = [e2 for e2 in src if all(e2[j] >= k[j] for j in range(3))]
    if len(cand) != 2:
        continue
    axis = [j for j in range(3) if cand[1][j] != k[j]]
    if len(axis) != 1 or any(cand[1][j] != k[j] for j in range(3) if j != axis[0]):
        raise SystemExit(f'non-unit two-source target {k} {cand}')
    ax = axis[0]
    if cand[1][ax] != k[ax] + 1 or cand[0] != k:
        raise SystemExit(f'unexpected two-source shape {k} {cand}')
    rows.append((i, k, cand, ax, k[ax] + 1, iv))

print(f'two-source rows: {len(rows)}; excluding .t126 leaves {len(rows)-1}')

out = []
out.append('import ThomsonNine.LocalSparseHessianAAABase\n')
out.append('open ThomsonNine Interval')
out.append('open ThomsonNine.LocalSparseHessianAAA')
out.append('open ThomsonNine.Interval.RatInterval\n')
out.append('namespace ThomsonNine.TwoSourceBinding\n')
audits = []
for i, k, cand, ax, n, iv in rows:
    if i == 126:
        continue
    tag = '_'.join(str(x) for x in k)
    qlo, qhi = q[k]
    r1lo, r1hi = Rint[k]
    r2lo, r2hi = Rint[cand[1]]
    alo, ahi = F(A[ax][0]), F(A[ax][1])
    plo, phi = mul((F(n), F(n)), (r2lo, r2hi))
    klo, khi = mul((plo, phi), (alo, ahi))
    out.append(interval(f'Q_{tag}', qlo, qhi, f'archived coefficientInterval .t{i}'))
    out.append(interval(f'R1_{tag}', r1lo, r1hi, f'source {cand[0]}'))
    out.append(interval(f'R2_{tag}', r2lo, r2hi, f'source {cand[1]}'))
    out.append(interval(f'A_{tag}', alo, ahi, f'center axis {ax}'))
    out.append(interval(f'P_{tag}', plo, phi, f'{n} * source {cand[1]}'))
    out.append(interval(f'K_{tag}', klo, khi, f'P * center axis {ax}'))
    out.append(f'''
theorem target_{tag}_interval_bound (c1 c2 a : ℝ)
    (h1 : R1_{tag}.mem c1) (h2 : R2_{tag}.mem c2) (ha : A_{tag}.mem a) :
    Q_{tag}.mem (c1 + ({n} * c2) * a) := by
  have hP : P_{tag}.mem ({n} * c2) := by
    refine mem_mul_of_bounds (mem_const ({n} : ℚ)) h2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (simp only [P_{tag}, R2_{tag}, RatInterval.const]; rw [Rat.le_iff]; norm_num)
  have hK : K_{tag}.mem (({n} * c2) * a) := by
    refine mem_mul_of_bounds hP ha ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (simp only [P_{tag}, K_{tag}, A_{tag}]; rw [Rat.le_iff]; norm_num)
  have hJ : (add R1_{tag} K_{tag}).mem (c1 + ({n} * c2) * a) := mem_add h1 hK
  refine mem_subset hJ ?_ ?_
  · change Q_{tag}.lo ≤ R1_{tag}.lo + K_{tag}.lo
    rw [Rat.le_iff]
    norm_num [Q_{tag}, R1_{tag}, K_{tag}]
  · change R1_{tag}.hi + K_{tag}.hi ≤ Q_{tag}.hi
    rw [Rat.le_iff]
    norm_num [Q_{tag}, R1_{tag}, K_{tag}]

theorem target_t{i:03d}_{tag}_interval_bound (c1 c2 a : ℝ)
    (h1 : R1_{tag}.mem c1) (h2 : R2_{tag}.mem c2) (ha : A_{tag}.mem a) :
    (coefficientInterval .t{i:03d}).mem (c1 + ({n} * c2) * a) := by
  have hQ : coefficientInterval .t{i:03d} = Q_{tag} := rfl
  rw [hQ]
  exact target_{tag}_interval_bound c1 c2 a h1 h2 ha
''')
    audits.append(f'#print axioms ThomsonNine.TwoSourceBinding.target_t{i:03d}_{tag}_interval_bound')
out.append('end ThomsonNine.TwoSourceBinding\n')
path = ROOT / 'formal/ThomsonNine/TwoSourceBindings.lean'
path.write_text('\n'.join(out))
print(f'wrote {path} ({path.stat().st_size} bytes), {len(audits)} theorems')
(ROOT / 'two_source_audits.txt').write_text('\n'.join(audits) + '\n')
