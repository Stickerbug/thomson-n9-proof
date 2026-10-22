#!/usr/bin/env python3
"""Export source intervals and the uniform grouped/gathered Lean bridge for AAA.

No archived numeric containment is assumed true by this exporter: Lean checks
literal interval well-formedness and the generic bridge. Numeric target bounds
are separate finite certificates. This does not identify the actual residual.
"""
from pathlib import Path
from fractions import Fraction
import argparse
import copy
import hashlib
import json

PV = Path(__file__).resolve().parent
OUT = PV / 'formal/ThomsonNine/AAAGroupedData.lean'
MANIFEST = PV / 'aaa_grouped_data_manifest.json'


def checked(hermite, aaa):
    source = hermite['R_coefficients']
    targets = aaa['shifted_polynomial']
    centers = aaa['new_center_intervals']
    if len(source) != 807 or len(targets) != 807:
        raise ValueError('expected 807 source and target terms')
    exponents = [tuple(e) for e, _ in source]
    if len(set(exponents)) != 807 or exponents != [tuple(e) for e, _ in targets]:
        raise ValueError('source/target exponent indexing differs')
    if len(centers) != 3:
        raise ValueError('expected three center intervals')
    for pair in [v for _, v in source] + centers:
        if len(pair) != 2 or Fraction(pair[0]) > Fraction(pair[1]):
            raise ValueError('invalid source/center interval')
    return source, centers


def rational(value):
    q = Fraction(value)
    return f'({q.numerator} / {q.denominator} : ℚ)'


def interval(pair):
    return '⟨' + ', '.join(rational(q) for q in pair) + ', by decide +kernel⟩'


def render(hermite, aaa):
    source, centers = checked(hermite, aaa)
    lines = ['''import ThomsonNine.GatheredBinding
import ThomsonNine.GroupedTranslation

/-! Generated exact source data and the uniform grouped/gathered bridge.
Source memberships are premises; the actual residual is not identified.
Archived target containments are discharged separately. -/
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace ThomsonNine.AAAGroupedData
open ThomsonNine.Interval ThomsonNine.Interval.RatInterval
open ThomsonNine.Interval.SparsePolynomial
open ThomsonNine.LocalSparseHessianAAA ThomsonNine.GatheredBinding

def sourceInterval : TermIndex → RatInterval
''']
    lines += [f'  | .t{i:03d} => {interval(pair)}\n' for i, (_, pair) in enumerate(source)]
    for i, pair in enumerate(centers):
        lines += [f'private def center{i} : RatInterval := {interval(pair)}\n']
    lines += ['''
def centerInterval : Fin 3 → RatInterval := ![center0, center1, center2]
def powerCache (i : Fin 3) (n : ℕ) : RatInterval := powInterval (centerInterval i) n

def computed (k : TermIndex) : RatInterval :=
  Grouped.groupedInterval exponents (exponents k) sourceInterval powerCache allTerms

/-- The explicit archived list covers every constructor, without an equality axiom. -/
theorem allTerms_complete : (k : TermIndex) → k ∈ allTerms
''']
    lines += [f'  | .t{i:03d} => List.getElem_mem (l := allTerms) (n := {i}) (by decide +kernel)\n' for i in range(807)]
    lines += ['''
/-- Uniform enclosure of the full gathered coefficient, for any of the 807 targets. -/
theorem computed_mem_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t))
    (ha : ∀ i, (centerInterval i).mem (a i)) (k : TermIndex) :
    (computed k).mem (gathered (exponents k) c a) := by
  exact Grouped.groupedInterval_mem exponents (exponents k) sourceInterval c
    powerCache a allTerms (fun t _ => hC t)
    (fun i n => powInterval_mem _ _ (ha i) n)

/-- A target can use the computed enclosure only with both checked endpoints. -/
theorem gathered_mem_of_bounds (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t))
    (ha : ∀ i, (centerInterval i).mem (a i)) (k : TermIndex)
    (hlo : (coefficientInterval k).lo ≤ (computed k).lo)
    (hhi : (computed k).hi ≤ (coefficientInterval k).hi) :
    (coefficientInterval k).mem (gathered (exponents k) c a) := by
  exact mem_subset (computed_mem_gathered c a hC ha k) hlo hhi

end ThomsonNine.AAAGroupedData
''']
    return ''.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    inputs = ['independent_hermite_RH_result.json', 'independent_local_00_AAA.json']
    hermite, aaa = [json.loads((PV / n).read_text()) for n in inputs]
    text = render(hermite, aaa)
    record = {'schema_version': 1, 'source_terms': 807, 'target_terms': 807,
              'scope': 'Uniform computed-interval bridge only; archived endpoint certificates separate; no actual residual binding.',
              'inputs_sha256': {n: hashlib.sha256((PV / n).read_bytes()).hexdigest() for n in inputs},
              'source_sha256': hashlib.sha256(text.encode()).hexdigest()}
    encoded = json.dumps(record, indent=2) + '\n'
    if args.self_test:
        for mutation in ['missing', 'exponent', 'reversed']:
            bad = copy.deepcopy(hermite)
            if mutation == 'missing': bad['R_coefficients'].pop()
            elif mutation == 'exponent': bad['R_coefficients'][0][0] = [99, 99, 99]
            else: bad['R_coefficients'][0][1] = ['1', '-1']
            try: checked(bad, aaa)
            except ValueError: continue
            raise RuntimeError('negative self-test accepted: ' + mutation)
    if args.check:
        if OUT.read_text() != text or MANIFEST.read_text() != encoded:
            raise SystemExit('AAA grouped data is stale')
    else:
        OUT.write_text(text)
        MANIFEST.write_text(encoded)
    print('AAA_GROUPED_DATA_PASS: 807 aligned source terms; generated/check=' + str(args.check))


if __name__ == '__main__':
    main()
