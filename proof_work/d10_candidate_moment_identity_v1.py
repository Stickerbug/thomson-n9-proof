#!/usr/bin/env python3
"""Check G_k identities by independent ordered-triangle sums in QQ[r]."""
from collections import Counter
from hashlib import sha256
from itertools import permutations
import json
from pathlib import Path
import time
from sympy.polys.domains import QQ
from sympy.polys.rings import ring
from candidate_low_rank import features


def main():
    started = time.monotonic()
    here = Path(__file__).resolve().parent
    source = here / 'candidate_triple_types_v1.json'
    feature_source = here / 'candidate_low_rank.py'
    output = here / 'd10_candidate_moment_identity_v1.json'
    data = json.loads(source.read_text())
    R, r = ring('r', QQ)
    one, zero = R.one, R.zero
    half = QQ(1, 2)
    nodes = {'A': one-3*half*r**2, 'B': 2*r**2-one,
             'C': half*r**2-one, 'D': -half*one,
             'F': half*r, 'G': -r, '1': one}
    pairs = {'A': 6, 'B': 3, 'C': 6, 'D': 3, 'F': 12, 'G': 6}
    assert data['pair_multiplicities'] == pairs
    assert len(data['triangle_types']) == 12
    assert sum(t['multiplicity'] for t in data['triangle_types']) == 84
    assert data['triangle_total'] == 84
    incidences, ordered = Counter(), Counter()
    for triangle in data['triangle_types']:
        labels, mult = triangle['labels'], triangle['multiplicity']
        assert len(labels) == 3 and isinstance(mult, int) and mult > 0
        for label in labels:
            assert label in pairs
            incidences[label] += mult
        # Do not deduplicate permutations: equal labels retain multiplicity.
        for triple in permutations(labels):
            ordered[triple] += mult
    assert dict(incidences) == {s: 7*n for s, n in pairs.items()}
    distinct_count = sum(ordered.values())
    assert distinct_count == 504
    for s, mult in pairs.items():
        for triple in [('1', s, s), (s, '1', s), (s, s, '1')]:
            ordered[triple] += 2*mult
    repeated_count = sum(ordered.values())-distinct_count
    assert repeated_count == 216
    ordered[('1', '1', '1')] += 9
    assert sum(ordered.values()) == 729
    assert all(ordered[(v, u, t)] == n for (u, v, t), n in ordered.items())
    powers = {s: [one] for s in nodes}
    for s, value in nodes.items():
        for i in range(1, 11):
            powers[s].append(powers[s][-1]*value)
    terms = []
    for (a, b, c), mult in sorted(ordered.items()):
        u, v, t = nodes[a], nodes[b], nodes[c]
        z, h = t-u*v, (one-u*u)*(one-v*v)
        q = [one, z]
        for k in range(1, 10):
            q.append(2*z*q[-1]-h*q[-2])
        terms.append((a, b, mult, q))
    blocks, failures = [], []
    def degree(p):
        return int(p.degree()) if p else 0
    def coefficients(p):
        return [{'power': int(m[0]), 'coefficient': str(c)}
                for m, c in sorted(p.items())]
    for k in range(11):
        m = 11-k
        p, c = features(r, k, m)
        p, c = list(map(R, p)), list(map(R, c))
        scale = 6*(one-r*r)**(k % 2)
        checked = max_lhs_degree = max_rhs_degree = 0
        block_failures = []
        # Contract t first, using only exact additions.
        weights = {}
        for a, b, mult, q in terms:
            weights[(a, b)] = weights.get((a, b), zero)+mult*q[k]
        for i in range(m):
            for j in range(i, m):
                lhs = sum((weight*powers[a][i]*powers[b][j]
                           for (a, b), weight in weights.items()), zero)
                rhs = scale*p[i]*p[j]+3*c[i]*c[j]
                difference = lhs-rhs
                max_lhs_degree = max(max_lhs_degree, degree(lhs))
                max_rhs_degree = max(max_rhs_degree, degree(rhs))
                checked += 1
                if difference:
                    failure = {'k': k, 'i': i, 'j': j,
                               'difference_lhs_minus_rhs': coefficients(difference)}
                    failures.append(failure)
                    block_failures.append(failure)
        block = {'k': k, 'm': m, 'upper_triangle_entries_checked': checked,
                 'full_entries_certified_using_proved_symmetry': m*m,
                 'all_differences_exact_zero': not block_failures,
                 'max_lhs_degree': max_lhs_degree, 'max_rhs_degree': max_rhs_degree}
        blocks.append(block)
        print(json.dumps(block), flush=True)
    result = {
        'status': 'exact_polynomial_identity_verified' if not failures else 'exact_polynomial_identity_FAILED',
        'coefficient_ring': 'QQ[r]', 'parameter': 'formal indeterminate r',
        'identity': 'G_k[i,j] = 6*(1-r^2)^(k mod 2)*p[i]*p[j] + 3*c[i]*c[j]',
        'definition': 'G_k[i,j] = sum_ordered_(x,y,z) u^i*v^j*Q_k(u,v,t)',
        'recurrence': ['Q_0=1', 'Q_1=t-u*v',
                       'Q_(k+1)=2*(t-u*v)*Q_k-(1-u^2)*(1-v^2)*Q_(k-1)'],
        'k_range': [0, 10], 'm': '11-k',
        'nodes': {s: str(nodes[s]) for s in pairs}, 'pair_multiplicities': pairs,
        'triangle_type_count': 12, 'unordered_distinct_triangles': 84,
        'ordered_distinct_terms': distinct_count,
        'ordered_exactly_two_equal_terms': repeated_count,
        'ordered_all_equal_terms': 9, 'ordered_total': sum(ordered.values()),
        'edge_triangle_incidence_check': dict(incidences),
        'i_j_symmetry_checked_from_ordered_term_multiplicities': True,
        'upper_triangle_entries_checked': sum(b['upper_triangle_entries_checked'] for b in blocks),
        'full_entries_certified_using_proved_symmetry': sum(b['full_entries_certified_using_proved_symmetry'] for b in blocks),
        'blocks': blocks, 'failures': failures,
        'inputs_sha256': {f.name: sha256(f.read_bytes()).hexdigest()
                          for f in [source, feature_source, Path(__file__).resolve()]},
        'trust_boundary': [
            'Triangle labels and multiplicities are input data, not independently derived from point coordinates here.',
            'Node polynomials are explicitly defined here; JSON inner_products, Gram factors, intervals and status fields are not used.',
            'Triangle totals and edge-triangle incidence are checked, but do not alone certify geometric realizability.',
            'LHS is independently constructed from triangle counts, repeated-vertex counts, and the Q recurrence.',
            'RHS is evaluated by importing candidate_low_rank.features with a formal QQ[r] generator.',
            'SymPy exact rational polynomial arithmetic, Python integer arithmetic, interpreter and source integrity are trusted.',
            'No numerical sampling, finite-field checks, algebraic-root reductions or interval substitution is used.',
            'This verifies polynomial identities only; no rank, geometric classification, global optimality, contact-system solvability, PSD certificate or residual nonnegativity is proved.',
            'For real |r|<=1 the displayed factorization implies PSD conditional on the verified identity; no broader certificate is checked.'
        ],
        'elapsed_seconds': time.monotonic()-started,
    }
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'status': result['status'], 'elapsed_seconds': result['elapsed_seconds'],
                      'output': str(output)}), flush=True)
    return 1 if failures else 0


if __name__ == '__main__':
    raise SystemExit(main())
