#!/usr/bin/env python3
"""Generate full 807-term gathered-coefficient bindings for all 3/4-source chain targets."""
import json, math
from pathlib import Path

ROOT = Path(__file__).resolve().parent
R = json.load(open(ROOT / 'independent_hermite_RH_result.json'))['R_coefficients']
src = [tuple(e) for e, _ in R]

rows = []
for i, (e, _) in enumerate(R):
    k = tuple(e)
    ss = [x for x in src if all(x[j] >= k[j] for j in range(3))]
    if len(ss) not in (3, 4):
        continue
    axes = [j for j in range(3) if len({x[j] for x in ss}) > 1]
    if len(axes) != 1:
        continue
    ax = axes[0]
    if any(len({x[j] for x in ss}) != 1 for j in range(3) if j != ax):
        continue
    if sorted({x[ax] for x in ss}) != list(range(k[ax], k[ax] + len(ss))):
        continue
    idx = [src.index(x) for x in ss]
    if idx != sorted(idx):
        raise SystemExit(f'non-manifest order {k} {idx}')
    rows.append((i, k, ss, ax, idx))

def vec(e):
    return '![' + ', '.join(str(x) for x in e) + ']'

out = ['import ThomsonNine.ChainBindings',
       'import ThomsonNine.GatheredBinding',
       'import ThomsonNine.SparseTranslation\n',
       'set_option maxRecDepth 100000',
       'set_option maxHeartbeats 1000000\n',
       'open ThomsonNine',
       'open ThomsonNine.LocalSparseHessianAAA',
       'open ThomsonNine.Interval',
       'open ThomsonNine.Interval.RatInterval',
       'open ThomsonNine.Interval.SparsePolynomial\n',
       'namespace ThomsonNine.GatheredChain\n']
audits = []
for i, k, ss, ax, idx in sorted(rows, key=lambda r: r[0]):
    tag = '_'.join(map(str, k)); m = len(ss)
    hargs = '\n'.join(f'    (h{j} : ThomsonNine.ChainBinding.R{j}_{tag}.mem (c .t{idx[j]:03d}))' for j in range(m))
    hes = []
    factors = [f'c .t{idx[0]:03d}']
    for j in range(1, m):
        n = math.comb(k[ax] + j, j)
        coeff = f'({n} * c .t{idx[j]:03d})'
        for _ in range(j):
            coeff = f'({coeff} * a {ax})'
        factors.append(coeff)
        if j == 1:
            proof = f'''    simp [expandedCoefficient, shiftFactor]
    norm_num
    ring'''
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
{hargs}
    (ha : ThomsonNine.ChainBinding.A_{tag}.mem (a {ax})) :
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
  exact ThomsonNine.ChainBinding.target_t{i:03d}_{tag}_interval_bound {callargs} (a := a {ax}) {hcall} ha
''')
    audits.append(f'#print axioms ThomsonNine.GatheredChain.t{i:03d}_gathered_mem')
out.append('end ThomsonNine.GatheredChain\n')
path = ROOT / 'formal/ThomsonNine/GatheredChain.lean'
path.write_text('\n'.join(out))
print(f'wrote {path} ({path.stat().st_size} bytes), {len(audits)} theorems')
(ROOT / 'gathered_chain_audits.txt').write_text('\n'.join(audits) + '\n')
