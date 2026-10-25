"""Exact rational Delsarte/Legendre lower bound for the 10-point problem.

This is a standalone certificate, not a Lean replay of the Thomson theorem.
It verifies an explicit polynomial minorant p <= (2-2t)^(-1/2) on [-1,1]
using the exact identity R=1-(2-2t)p^2 and Bernstein subdivision.  All
arithmetic after the hard-coded rational coefficients uses Fraction only.
"""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json

# Coefficients in the Legendre basis P_0,...,P_12.  They are deliberately
# rounded down from the sampled LP solution to leave a strict certificate gap.
COEFF = [
    F(41269, 50000), F(25267, 50000), F(3233, 12500), F(10131, 100000),
    F(47, 2000), F(0), F(0), F(109, 50000), F(131, 100000),
    F(0), F(0), F(0), F(0),
]


def add(a, b):
    return [(a[i] if i < len(a) else F(0)) +
            (b[i] if i < len(b) else F(0))
            for i in range(max(len(a), len(b)))]


def scale(a, s):
    return [v * s for v in a]


def mul(a, b):
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def legendre_polynomials(degree):
    P = [[F(1)], [F(0), F(1)]]
    for k in range(2, degree + 1):
        # (k P_k) = (2k-1)t P_{k-1} - (k-1)P_{k-2}
        P.append(scale(add(scale([F(0)] + P[-1], 2 * k - 1),
                            scale(P[-2], 1 - k)), F(1, k)))
    return P[:degree + 1]


def bernstein_coefficients_power(poly):
    """Bernstein coefficients after t=2x-1 on x in [0,1]."""
    degree = len(poly) - 1
    power = [F(0)] * (degree + 1)
    for j, c in enumerate(poly):
        for k in range(j + 1):
            power[k] += c * comb(j, k) * (2 ** k) * ((-1) ** (j - k))
    return [sum((power[j] * F(comb(k, j), comb(degree, j))
                 for j in range(k + 1)), F(0))
            for k in range(degree + 1)]


def certify_nonnegative(bernstein, max_depth=40):
    """Exact de Casteljau subdivision; return leaf/depth statistics."""
    degree = len(bernstein) - 1
    stack = [(bernstein, 0, F(0), F(1))]
    leaves = []
    while stack:
        coeff, depth, lo, hi = stack.pop()
        if min(coeff) >= 0:
            leaves.append((depth, lo, hi))
            continue
        if max(coeff) < 0:
            raise AssertionError(("negative Bernstein leaf", depth, lo, hi))
        if depth >= max_depth:
            raise AssertionError(("subdivision limit", depth, lo, hi))
        rows = [coeff]
        for _ in range(degree):
            rows.append([(u + v) / 2 for u, v in zip(rows[-1], rows[-1][1:])])
        left = [row[0] for row in rows]
        right = [row[-1] for row in rows][::-1]
        mid = (lo + hi) / 2
        stack.append((left, depth + 1, lo, mid))
        stack.append((right, depth + 1, mid, hi))
    return leaves


def run():
    assert len(COEFF) == 13 and all(c >= 0 for c in COEFF[1:])
    P = legendre_polynomials(len(COEFF) - 1)
    p = [F(0)]
    for c, q in zip(COEFF, P):
        p = add(p, scale(q, c))
    # If R >= 0 then |p(t)| <= 1/sqrt(2-2t), hence p(t) is a minorant.
    residual = add([F(1)], scale(mul([F(2), F(-2)], mul(p, p)), -1))
    bernstein = bernstein_coefficients_power(residual)
    leaves = certify_nonnegative(bernstein)
    n = 10
    lower = F(n * n, 2) * COEFF[0] - F(n, 2) * sum(COEFF)
    result = {
        "status": "EXACT_FRACTION_BERNSTEIN_CERTIFICATE",
        "scope": "unconditional Delsarte/Legendre lower bound for ten sphere points",
        "degree": len(COEFF) - 1,
        "legendre_coefficients": [str(c) for c in COEFF],
        "residual_definition": "R(t)=1-(2-2*t)*p(t)^2",
        "residual_power_degree": len(residual) - 1,
        "bernstein_leaf_count": len(leaves),
        "bernstein_max_depth": max(d for d, _, _ in leaves),
        "lower_bound_exact": str(lower),
        "lower_bound_decimal": float(lower),
        "candidate_energy_decimal": 32.71694946014759,
        "candidate_gap_decimal": 32.71694946014759 - float(lower),
        "trust_boundary": [
            "Fraction arithmetic and Bernstein subdivision are replayed by this script.",
            "A Lean theorem connecting this polynomial to the n=10 Thomson energy is not yet present.",
            "The bound is below the D4d candidate and therefore does not prove optimality.",
        ],
    }
    out = Path(__file__).with_suffix('.json')
    out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
    return result


if __name__ == '__main__':
    run()
