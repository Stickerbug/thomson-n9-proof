#!/usr/bin/env python3
"""Generate full 807-term gathered-coefficient bindings for single-source targets."""
import json
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parent
R = json.load(open(ROOT / 'independent_hermite_RH_result.json'))['R_coefficients']
Q = json.load(open(ROOT / 'independent_local_00_AAA.json'))['shifted_polynomial']
src = [tuple(e) for e, _ in R]
q = {tuple(e): (F(v[0]), F(v[1])) for e, v in Q}

rows = []
for i, (e, iv) in enumerate(R):
    k = tuple(e)
    ss = [x for x in src if all(x[j] >= k[j] for j in range(3))]
    if len(ss) == 1:
        rows.append((i, k, iv))

def rat(x):
    f = F(x); return f'(({f.numerator} : ℚ) / {f.denominator})'

def interval(name, lo, hi):
    return f'def {name} : RatInterval := ⟨{rat(lo)}, {rat(hi)}, by rw [Rat.le_iff]; norm_num⟩'

def vec(e):
    return '![' + ', '.join(str(x) for x in e) + ']'

out = ['import ThomsonNine.GatheredBinding',
       'import ThomsonNine.SparseTranslation\n',
       'set_option maxRecDepth 100000\n',
       'open ThomsonNine',
       'open ThomsonNine.LocalSparseHessianAAA',
       'open ThomsonNine.Interval',
       'open ThomsonNine.Interval.RatInterval',
       'open ThomsonNine.Interval.SparsePolynomial\n',
       'namespace ThomsonNine.SingleSource\n']
audits = []
for i, k, iv in sorted(rows):
    tag = '_'.join(map(str, k))
    rlo, rhi = F(iv[0]), F(iv[1]); qlo, qhi = q[k]
    out.append(interval(f'Q_{tag}', qlo, qhi))
    out.append(interval(f'R_{tag}', rlo, rhi))
    out.append(f'''theorem target_{tag}_interval (c : ℝ) (h : R_{tag}.mem c) :
    (coefficientInterval .t{i:03d}).mem c := by
  have hQ : coefficientInterval .t{i:03d} = Q_{tag} := rfl
  rw [hQ]
  refine mem_subset h ?_ ?_
  · change Q_{tag}.lo ≤ R_{tag}.lo
    rw [Rat.le_iff]
    norm_num [Q_{tag}, R_{tag}]
  · change R_{tag}.hi ≤ Q_{tag}.hi
    rw [Rat.le_iff]
    norm_num [Q_{tag}, R_{tag}]

theorem t{i:03d}_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h : R_{tag}.mem (c .t{i:03d})) :
    (coefficientInterval .t{i:03d}).mem (ThomsonNine.GatheredBinding.gathered (exponents .t{i:03d}) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t{i:03d} i ≤ exponents t i)) = [.t{i:03d}] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he : expandedCoefficient (exponents .t{i:03d}) (exponents .t{i:03d}) (c .t{i:03d}) a = c .t{i:03d} := by
    have hv : exponents .t{i:03d} = {vec(k)} := rfl
    rw [hv]
    simp [expandedCoefficient, shiftFactor]
  rw [he]
  exact target_{tag}_interval (c .t{i:03d}) h
''')
    audits.append(f'#print axioms ThomsonNine.SingleSource.t{i:03d}_gathered_mem')
out.append('end ThomsonNine.SingleSource\n')
path = ROOT / 'formal/ThomsonNine/SingleSourceBindings.lean'
path.write_text('\n'.join(out))
print(f'wrote {path} ({path.stat().st_size} bytes), {len(audits)} theorems')
(ROOT / 'single_source_audits.txt').write_text('\n'.join(audits) + '\n')
