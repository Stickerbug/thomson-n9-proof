#!/usr/bin/env python3
"""Generate full 807-term gathered-coefficient bindings for all two-source targets except .t126."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
R = json.load(open(ROOT / 'independent_hermite_RH_result.json'))['R_coefficients']
src = [tuple(e) for e, _ in R]

rows = []
for i, (e, iv) in enumerate(R):
    k = tuple(e)
    cand = [e2 for e2 in src if all(e2[j] >= k[j] for j in range(3))]
    if len(cand) != 2 or i == 126:
        continue
    axis = [j for j in range(3) if cand[1][j] != k[j]]
    if len(axis) != 1:
        raise SystemExit(f'non-unit two-source target {k} {cand}')
    ax = axis[0]
    if cand[1][ax] != k[ax] + 1 or cand[0] != k:
        raise SystemExit(f'unexpected two-source shape {k} {cand}')
    rows.append((i, k, cand, ax, k[ax] + 1))

def vec(e):
    return '![' + ', '.join(str(x) for x in e) + ']'

out = []
out.append('import ThomsonNine.TwoSourceBindings')
out.append('import ThomsonNine.GatheredBinding')
out.append('import ThomsonNine.SparseTranslation\n')
out.append('set_option maxRecDepth 100000\n')
out.append('open ThomsonNine')
out.append('open ThomsonNine.LocalSparseHessianAAA')
out.append('open ThomsonNine.Interval')
out.append('open ThomsonNine.Interval.RatInterval')
out.append('open ThomsonNine.Interval.SparsePolynomial\n')
out.append('namespace ThomsonNine.GatheredTwoSource\n')
audits = []
for i, k, cand, ax, n in sorted(rows, key=lambda r: r[0]):
    tag = '_'.join(str(x) for x in k)
    j = src.index(cand[1])
    if j < 0:
        raise SystemExit(f'missing source index {cand[1]}')
    out.append(f'''theorem t{i:03d}_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : ThomsonNine.TwoSourceBinding.R1_{tag}.mem (c .t{i:03d}))
    (h1 : ThomsonNine.TwoSourceBinding.R2_{tag}.mem (c .t{j:03d}))
    (ha : ThomsonNine.TwoSourceBinding.A_{tag}.mem (a {ax})) :
    (coefficientInterval .t{i:03d}).mem (ThomsonNine.GatheredBinding.gathered (exponents .t{i:03d}) c a) := by
  have hf : ThomsonNine.GatheredBinding.allTerms.filter
      (fun t => decide (∀ i, exponents .t{i:03d} i ≤ exponents t i)) = [.t{i:03d}, .t{j:03d}] := by
    rfl
  rw [ThomsonNine.GatheredBinding.gathered, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have he0 : expandedCoefficient (exponents .t{i:03d}) (exponents .t{i:03d}) (c .t{i:03d}) a = c .t{i:03d} := by
    have h : exponents .t{i:03d} = {vec(k)} := rfl
    rw [h]
    simp [expandedCoefficient, shiftFactor]
  have he1 : expandedCoefficient (exponents .t{j:03d}) (exponents .t{i:03d}) (c .t{j:03d}) a = ({n} * c .t{j:03d}) * a {ax} := by
    have hk : exponents .t{i:03d} = {vec(k)} := rfl
    have h : exponents .t{j:03d} = {vec(cand[1])} := rfl
    rw [hk, h]
    simp [expandedCoefficient, shiftFactor]
    ring
  rw [he0, he1]
  exact ThomsonNine.TwoSourceBinding.target_t{i:03d}_{tag}_interval_bound (c .t{i:03d}) (c .t{j:03d}) (a {ax}) h0 h1 ha
''')
    audits.append(f'#print axioms ThomsonNine.GatheredTwoSource.t{i:03d}_gathered_mem')
out.append('end ThomsonNine.GatheredTwoSource\n')
path = ROOT / 'formal/ThomsonNine/GatheredTwoSource.lean'
path.write_text('\n'.join(out))
print(f'wrote {path} ({path.stat().st_size} bytes), {len(audits)} theorems')
(ROOT / 'gathered_two_source_audits.txt').write_text('\n'.join(audits) + '\n')
