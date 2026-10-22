#!/usr/bin/env python3
"""Reproduce the integer interval data, fixed grouping tree and finite Lean bounds.

Generation is not a proof. Each literal source widening, tree permutation,
coordinate compatibility and archived containment is checked by Lean's kernel.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import OrderedDict
import argparse
import copy
import hashlib
import json

PV = Path(__file__).resolve().parent
FORMAL = PV / 'formal/ThomsonNine'
TEMPLATES = PV / 'fixed_inputs'
MANIFEST = PV / 'aaa_fixed_tree_manifest.json'
BITS = 768
SCALE = 1 << BITS
INPUTS = ['independent_hermite_RH_result.json', 'independent_local_00_AAA.json']


def checked(R, J):
    source, target, centers = R['R_coefficients'], J['shifted_polynomial'], J['new_center_intervals']
    if len(source) != 807 or len(target) != 807 or len(centers) != 3:
        raise ValueError('expected 807 aligned sources and targets and three centers')
    es = [tuple(e) for e, _ in source]
    if len(set(es)) != 807 or es != [tuple(e) for e, _ in target]:
        raise ValueError('source/target exponent indexing differs')
    if any(len(e) != 3 or any(type(n) is not int or not 0 <= n <= 27 for n in e) for e in es):
        raise ValueError('invalid exponent')
    for pair in [I for _, I in source] + [I for _, I in target] + centers:
        if len(pair) != 2 or F(pair[0]) > F(pair[1]):
            raise ValueError('invalid interval')
    return [(e, tuple(map(F, I))) for e, (_, I) in zip(es, source)], list(map(lambda I: tuple(map(F, I)), centers))


def pair(I):
    return (int((I[0]*SCALE).__floor__()), int((I[1]*SCALE).__ceil__()))


def bound(I):
    return '⟨' + ', '.join(str(x) if x >= 0 else f'({x})' for x in pair(I)) + '⟩'


def template(name, replacements):
    s = (TEMPLATES / (name + '.lean.in')).read_text()
    for key, value in replacements.items():
        marker = '@@' + key + '@@'
        if s.count(marker) != 1:
            raise ValueError('template marker differs: ' + marker)
        s = s.replace(marker, value)
    if '@@' in s:
        raise ValueError('unreplaced template marker')
    return s


def render(R, J):
    src, centers = checked(R, J)
    out = {}
    source_text = ''.join(f'  | .t{i:03d} => {bound(I)}\n' for i, (_, I) in enumerate(src))
    out['AAAFixedData'] = template('AAAFixedData', {'SOURCE': source_text.rstrip(),
                                                  'CENTER': '![' + ', '.join(map(bound, centers)) + ']'})
    entries = []
    for i, (e, I) in enumerate(src):
        entries.append(f'⟨.t{i:03d}, {e[0]}, {e[1]}, {e[2]}, {bound(I)}⟩')
    out['AAAIndexedData'] = template('AAAIndexedData', {'ENTRIES': '[\n  ' + ',\n  '.join(entries) + '\n]'} )
    groups = OrderedDict()
    for i, (e, _) in enumerate(src):
        groups.setdefault(e[2], OrderedDict()).setdefault(e[1], []).append(i)
    inds, tree = [], []
    for t, G in groups.items():
        inds.append(f'({t}, [' + ', '.join(f'({v}, [' + ', '.join(map(str, ids)) + '])' for v, ids in G.items()) + '])')
        tree.append(f'({t}, [\n    ' + ',\n    '.join(f'({v}, [\n      ' + ',\n      '.join(entries[i] for i in ids) + '\n    ])' for v, ids in G.items()) + '\n  ])')
    out['AAATreeData'] = template('AAATreeData', {'INDICES': '[\n  ' + ',\n  '.join(inds) + '\n]',
                                               'TREE': '[\n  ' + ',\n  '.join(tree) + '\n]'})
    header = '''set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
noncomputable section
namespace ThomsonNine.AAAFixedBounds
open ThomsonNine.LocalSparseHessianAAA ThomsonNine.GatheredBinding
open ThomsonNine.AAAFixedData
'''
    for chunk, start in enumerate(range(0, 807, 96)):
        s = 'import ThomsonNine.AAATreeData\n' + header
        for i in range(start, min(start+96, 807)):
            s += f'''
theorem bounds{i:03d} :
    (precision : ℚ)*(coefficientInterval .t{i:03d}).lo ≤ ((AAATreeData.computed .t{i:03d}).lo : ℚ) ∧
    ((AAATreeData.computed .t{i:03d}).hi : ℚ) ≤ (precision : ℚ)*(coefficientInterval .t{i:03d}).hi := by
  decide +kernel
'''
        out[f'AAAFixedBounds{chunk:02d}'] = s + '\nend ThomsonNine.AAAFixedBounds\n'
    s = 'import ThomsonNine.LocalSparseHessianAAA\n' + ''.join(f'import ThomsonNine.AAAFixedBounds{n:02d}\n' for n in range(9)) + '''
noncomputable section
namespace ThomsonNine.AAAFixedComplete
open ThomsonNine.LocalSparseHessianAAA ThomsonNine.GatheredBinding
open ThomsonNine.AAAGroupedData ThomsonNine.AAAFixedData ThomsonNine.AAAFixedBounds

/-- Every archived target interval contains its full gathered coefficient,
conditional on one fixed source family and one fixed center. -/
theorem bounds : (k : TermIndex) →
    (precision : ℚ)*(coefficientInterval k).lo ≤ ((AAATreeData.computed k).lo : ℚ) ∧
    ((AAATreeData.computed k).hi : ℚ) ≤ (precision : ℚ)*(coefficientInterval k).hi
'''
    s += ''.join(f'  | .t{i:03d} => bounds{i:03d}\n' for i in range(807))
    s += '''
theorem all_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i))
    (k : TermIndex) : (coefficientInterval k).mem (gathered (exponents k) c a) :=
  AAATreeData.gathered_of_bounds c a hC ha k (bounds k)
'''
    s += """
/-- The existing full AAA H00 certificate now applies to the entire gathered
coefficient family. This still does not identify the actual residual. -/
theorem gathered_h00_mem (c : TermIndex → ℝ) (a x : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i))
    (hx : ∀ i, (relativeBox i).mem (x i)) :
    targetH00.mem
      (Interval.SparsePolynomial.axisDeriv
        (Interval.SparsePolynomial.axisDeriv
          (fun y => Interval.SparsePolynomial.eval exponents
            (fun k => gathered (exponents k) c a) y terms) 0) 0 x) :=
  actual_h00_mem (fun k => gathered (exponents k) c a) x (all_gathered c a hC ha) hx
"""
    # These targets were open at the 293-target baseline. Historical declarations
    # remain intact; adding only the missing pointwise corollaries avoids duplicates.
    baseline = json.loads((PV / 'fixed_inputs/baseline_targets.json').read_text())
    if len(baseline) != 293 or len(set(baseline)) != 293 or any(type(i) is not int or not 0 <= i < 807 for i in baseline):
        raise ValueError('invalid 293-target historical baseline')
    new = sorted(set(range(807)) - set(baseline))
    for i in new:
        s += f'''
theorem t{i:03d}_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t{i:03d}).mem (gathered (exponents .t{i:03d}) c a) :=
  all_gathered c a hC ha .t{i:03d}
'''
    out['AAAFixedComplete'] = s + '\nend ThomsonNine.AAAFixedComplete\n'
    return out, new


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    R, J = [json.loads((PV / n).read_text()) for n in INPUTS]
    outputs, new = render(R, J)
    if args.self_test:
        for mutation in ['missing', 'index', 'reversed', 'exponent']:
            bad = copy.deepcopy(R)
            if mutation == 'missing': bad['R_coefficients'].pop()
            elif mutation == 'index': bad['R_coefficients'][0], bad['R_coefficients'][1] = bad['R_coefficients'][1], bad['R_coefficients'][0]
            elif mutation == 'reversed': bad['R_coefficients'][0][1] = ['1', '-1']
            else: bad['R_coefficients'][0][0] = [28, 0, 0]
            try: checked(bad, J)
            except ValueError: continue
            raise RuntimeError('negative self-test accepted: ' + mutation)
    manifest = {'schema_version': 1, 'bits': BITS, 'source_terms': 807, 'target_terms': 807,
                'generated_modules': list(outputs), 'new_pointwise_targets': new,
                'scope': 'Kernel-checked conditional archived gathered bounds; no actual residual binding or global theorem.',
                'input_sha256': {n: hashlib.sha256((PV/n).read_bytes()).hexdigest() for n in INPUTS},
                'template_sha256': {str(p.relative_to(PV)): hashlib.sha256(p.read_bytes()).hexdigest()
                                    for p in sorted(TEMPLATES.iterdir()) if p.is_file()},
                'source_sha256': {n: hashlib.sha256(s.encode()).hexdigest() for n, s in outputs.items()}}
    record = json.dumps(manifest, indent=2) + '\n'
    if args.check:
        if MANIFEST.read_text() != record or any((FORMAL/(n+'.lean')).read_text() != s for n, s in outputs.items()):
            raise SystemExit('fixed tree generated data is stale')
    else:
        for n, s in outputs.items():
            dest = FORMAL/(n+'.lean')
            if not dest.exists() or dest.read_text() != s: dest.write_text(s)
        MANIFEST.write_text(record)
    print(f'AAA_FIXED_TREE_PASS: {len(outputs)} modules; 807 bounds; {len(new)} new pointwise corollaries; check={args.check}')


if __name__ == '__main__':
    main()
