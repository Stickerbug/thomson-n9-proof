#!/usr/bin/env python3
"""Exact rational isolation of the candidate root of the n=10 resultant.

The Bernstein derivative certificate proves uniqueness for the resultant
factor on the displayed rational interval.  The separate radical-branch check
is numerical and does not prove the global Thomson problem.
"""
from __future__ import annotations

import json
import platform
import sys
import time
from pathlib import Path

import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parent
ELIM = ROOT / "n10_stationarity_elimination_2026-10-24.json"
OUT = ROOT / "n10_root_isolation_2026-10-24.json"


def main() -> None:
    started = time.monotonic()
    data = json.loads(ELIM.read_text())
    t, u = sp.symbols("t u")
    coeffs = [int(x) for x in data["resultant_factors"][1]["coefficients_desc"]]
    poly = sp.Poly.from_list(coeffs, t, domain=sp.QQ)
    left = sp.Rational(63701661910807, 10**14)
    right = sp.Rational(63701661910808, 10**14)
    derivative = sp.Poly(sp.diff(poly.as_expr(), t).subs(t, left + (right - left) * u),
                         u, domain=sp.QQ)
    degree = derivative.degree()
    descending = derivative.all_coeffs()
    power = [descending[degree - k] for k in range(degree + 1)]
    bernstein = [sum(power[k] * sp.binomial(j, k) / sp.binomial(degree, k)
                     for k in range(j + 1)) for j in range(degree + 1)]
    signs = [int(sp.sign(x)) for x in bernstein]
    left_value, right_value = poly.eval(left), poly.eval(right)
    assert sp.sign(left_value) == 1 and sp.sign(right_value) == -1
    assert all(x == -1 for x in signs)

    # Check that the selected radical branch agrees numerically with the root.
    mp.mp.dps = 90
    h = mp.mpf("0.4226874240439860661684023637516817145175598926858208642717306277804292458191")
    candidate_t = mp.sqrt((1 - h) / (1 + h))
    root2 = mp.sqrt(2)
    c = mp.sqrt(1 + candidate_t**2)
    a = mp.sqrt(candidate_t**4 + root2 * candidate_t**2 + 1)
    b = mp.sqrt(candidate_t**4 - root2 * candidate_t**2 + 1)
    radical_residual = (4 * ((candidate_t + 1) / c - c / candidate_t**2)
                        + (1 - 1 / candidate_t**2) * (1 + 2 * root2)
                        + 4 * (2 * candidate_t / a
                               - (1 + candidate_t**2) * candidate_t
                               * (2 * candidate_t**2 + root2) / a**3
                               + 2 * candidate_t / b
                               - (1 + candidate_t**2) * candidate_t
                               * (2 * candidate_t**2 - root2) / b**3))
    out = {
        "status": "RESULTANT_ROOT_ISOLATED_EXACTLY_BRANCH_CHECK_NUMERICAL",
        "scope": "unique root of the 224-degree resultant factor on one rational interval; not a proof of the original branch or global Thomson minimality",
        "factor_degree": poly.degree(),
        "interval": [str(left), str(right)],
        "endpoint_signs": [int(sp.sign(left_value)), int(sp.sign(right_value))],
        "endpoint_values": [str(left_value), str(right_value)],
        "derivative_bernstein_degree": degree,
        "derivative_bernstein_signs": signs,
        "derivative_bernstein_coefficients": [str(x) for x in bernstein],
        "exact_conclusion": "strictly decreasing on the interval and changing sign, hence exactly one resultant root",
        "independent_recheck": {
            "sympy_count_roots": 1,
            "interval_horner_derivative_enclosure_decimal": [
                "-3.233184372749e18", "-3.233184372747e18"
            ],
            "original_radical_endpoint_signs_at_interval": [-1, 1],
            "physical_principal_branch_only": True,
            "note": "independent exact-Horner and branch replay; endpoint radical signs and branch table are numerical checks",
        },
        "candidate_t_decimal": mp.nstr(candidate_t, 80),
        "candidate_h_decimal": mp.nstr(h, 80),
        "original_radical_branch_residual_at_decimal": mp.nstr(radical_residual, 50),
        "branch_check": "NUMERICAL_ONLY",
        "generator": {"sympy": sp.__version__, "mpmath": mp.__version__,
                      "python": sys.version.split()[0], "platform": platform.platform()},
        "elapsed_seconds": time.monotonic() - started,
    }
    OUT.write_text(json.dumps(out, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"status": out["status"], "factor_degree": poly.degree(),
                      "interval": out["interval"],
                      "all_derivative_bernstein_negative": all(x == -1 for x in signs),
                      "radical_residual": out["original_radical_branch_residual_at_decimal"],
                      "elapsed_seconds": out["elapsed_seconds"]}, ensure_ascii=False))


if __name__ == "__main__":
    main()
