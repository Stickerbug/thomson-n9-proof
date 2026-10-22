#!/usr/bin/env python3
"""Numeric feasibility of bounded-precision caches; NOT a Lean certificate."""
from pathlib import Path
from fractions import Fraction as F
from math import comb
import argparse
import hashlib
import json
import time

PV = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bits', type=int, nargs='+', default=[768, 1024])
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if any(not 640 <= b <= 4096 for b in args.bits):
        parser.error('precision must be between 640 and 4096 bits')
    names = ['independent_hermite_RH_result.json', 'independent_local_00_AAA.json']
    R, J = [json.loads((PV / n).read_text()) for n in names]
    source = [(tuple(e), tuple(map(F, I))) for e, I in R['R_coefficients']]
    target = {tuple(e): tuple(map(F, I)) for e, I in J['shifted_polynomial']}
    centers = [tuple(map(F, I)) for I in J['new_center_intervals']]
    assert len(source) == len(target) == 807
    def mul(I, K):
        products = [a*b for a in I for b in K]
        return min(products), max(products)
    def add(I, K): return I[0]+K[0], I[1]+K[1]
    exact_powers = []
    for A in centers:
        powers = [(F(1), F(1))]
        for _ in range(27): powers.append(mul(powers[-1], A))
        exact_powers.append(powers)
    cases = []
    for bits in args.bits:
        start = time.monotonic()
        scale = 1 << bits
        def rounded(I): return F((I[0]*scale).__floor__(), scale), F((I[1]*scale).__ceil__(), scale)
        powers = [[rounded(I) for I in P] for P in exact_powers]
        bad = []
        max_den_bits = 0
        for index, (k, _) in enumerate(source):
            groups = {}
            for e, I in source:
                if not all(e[j] >= k[j] for j in range(3)): continue
                factor = tuple(F(comb(e[0], k[0])) * x for x in powers[0][e[0]-k[0]])
                key = e[1], e[2]
                groups[key] = add(groups.get(key, (F(0), F(0))), mul(I, factor))
            second = {}
            for (v, t), I in groups.items():
                I = rounded(I)
                factor = tuple(F(comb(v, k[1])) * x for x in powers[1][v-k[1]])
                second[t] = add(second.get(t, (F(0), F(0))), mul(I, factor))
            final = (F(0), F(0))
            for t, I in second.items():
                I = rounded(I)
                factor = tuple(F(comb(t, k[2])) * x for x in powers[2][t-k[2]])
                final = add(final, mul(I, factor))
            max_den_bits = max(max_den_bits, *(x.denominator.bit_length() for x in final))
            if not target[k][0] <= final[0] <= final[1] <= target[k][1]: bad.append(index)
        cases.append({'bits': bits, 'seconds': time.monotonic()-start, 'contained': 807-len(bad),
                      'not_contained_targets': bad, 'max_final_denominator_bits': max_den_bits})
    record = {'scope': 'Exact Python feasibility only; cache widening soundness and finite witnesses still require Lean proofs.',
              'input_sha256': {n: hashlib.sha256((PV/n).read_bytes()).hexdigest() for n in names}, 'cases': cases}
    text = json.dumps(record, indent=2) + '\n'
    if args.output: args.output.write_text(text)
    print(text)


if __name__ == '__main__':
    main()
