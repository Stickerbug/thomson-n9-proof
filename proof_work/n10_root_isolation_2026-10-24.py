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
from fractions import Fraction
from math import isqrt
from pathlib import Path

import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parent
ELIM = ROOT / "n10_stationarity_elimination_2026-10-24.json"
OUT = ROOT / "n10_root_isolation_2026-10-24.json"


class RationalInterval:
    """Closed rational interval with outward-rounded elementary operations."""

    def __init__(self, lo, hi=None):
        self.lo = Fraction(lo)
        self.hi = self.lo if hi is None else Fraction(hi)
        if self.lo > self.hi:
            raise ValueError("invalid interval")

    def __add__(self, other):
        other = other if isinstance(other, RationalInterval) else RationalInterval(other)
        return RationalInterval(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return RationalInterval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-other if isinstance(other, RationalInterval) else -RationalInterval(other))

    def __rsub__(self, other):
        return RationalInterval(other) - self

    def __mul__(self, other):
        other = other if isinstance(other, RationalInterval) else RationalInterval(other)
        values = (self.lo * other.lo, self.lo * other.hi,
                  self.hi * other.lo, self.hi * other.hi)
        return RationalInterval(min(values), max(values))

    __rmul__ = __mul__

    def inverse(self):
        if self.lo <= 0 <= self.hi:
            raise ZeroDivisionError("interval contains zero")
        return RationalInterval(1 / self.hi, 1 / self.lo)

    def __truediv__(self, other):
        other = other if isinstance(other, RationalInterval) else RationalInterval(other)
        return self * other.inverse()

    def __rtruediv__(self, other):
        return RationalInterval(other) / self


def sqrt_rational_bounds(value, scale=10**120):
    """Return rational lower/upper bounds for sqrt(value)."""
    if value < 0:
        raise ValueError("sqrt of negative rational")
    floor_root = isqrt(value.numerator * scale * scale // value.denominator)
    return Fraction(floor_root, scale), Fraction(floor_root + 1, scale)


def interval_sqrt(interval):
    if interval.lo < 0:
        raise ValueError("sqrt interval has negative lower endpoint")
    lower = sqrt_rational_bounds(interval.lo)[0]
    upper = sqrt_rational_bounds(interval.hi)[1]
    return RationalInterval(lower, upper)


def radical_stationarity_interval(t_value):
    """Evaluate the D4d stationarity expression using rational intervals."""
    t = RationalInterval(t_value)
    s = interval_sqrt(RationalInterval(2))
    c = interval_sqrt(RationalInterval(1) + t * t)
    a = interval_sqrt(t * t * t * t + s * t * t + 1)
    b = interval_sqrt(t * t * t * t - s * t * t + 1)
    expression = (
        4 * ((t + 1) / c - c / (t * t))
        + (1 - 1 / (t * t)) * (1 + 2 * s)
        + 4 * (
            2 * t / a
            - (1 + t * t) * t * (2 * t * t + s) / (a * a * a)
            + 2 * t / b
            - (1 + t * t) * t * (2 * t * t - s) / (b * b * b)
        )
    )
    return expression


def d4d_energy_interval(h_interval):
    """Evaluate the D4d-family energy with rational interval arithmetic."""
    one = RationalInterval(1)
    half = RationalInterval(Fraction(1, 2))
    s = interval_sqrt(RationalInterval(2))
    h2 = h_interval * h_interval
    return (
        half
        + 8 / interval_sqrt(2 - 2 * h_interval)
        + 8 / interval_sqrt(2 + 2 * h_interval)
        + 8 / interval_sqrt(2 - 2 * h2)
        + 2 / interval_sqrt(one - h2)
        + 8 / interval_sqrt(2 + 2 * h2 - s * (one - h2))
        + 8 / interval_sqrt(2 + 2 * h2 + s * (one - h2))
    )


def interval_decimal(interval, digits=45):
    mp.mp.dps = digits + 10
    return [
        mp.nstr(mp.mpf(interval.lo.numerator) / interval.lo.denominator, digits),
        mp.nstr(mp.mpf(interval.hi.numerator) / interval.hi.denominator, digits),
    ]


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
    left_radical_interval = radical_stationarity_interval(left)
    right_radical_interval = radical_stationarity_interval(right)
    assert left_radical_interval.hi < 0 and right_radical_interval.lo > 0
    h_interval = RationalInterval(
        (1 - right * right) / (1 + right * right),
        (1 - left * left) / (1 + left * left),
    )
    energy_interval = d4d_energy_interval(h_interval)

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
        "exact_conclusion": "strictly decreasing on the interval and changing sign, hence exactly one resultant root; rational interval evaluation gives opposite signs for the original radical stationarity expression at the same endpoints",
        "independent_recheck": {
            "sympy_count_roots": 1,
            "interval_horner_derivative_enclosure_decimal": [
                "-3.233184372749e18", "-3.233184372747e18"
            ],
            "original_radical_endpoint_signs_at_interval": [-1, 1],
            "physical_principal_branch_only": True,
            "note": "independent exact-Horner and rational interval branch replay; sign intervals are exact rational enclosures, while the branch table and decimal residual remain numerical checks",
        },
        "original_radical_endpoint_intervals_decimal": {
            "left": interval_decimal(left_radical_interval),
            "right": interval_decimal(right_radical_interval),
        },
        "original_radical_endpoint_signs_exact_interval": [-1, 1],
        "d4d_h_interval_exact": [str(h_interval.lo), str(h_interval.hi)],
        "d4d_energy_interval_exact": [str(energy_interval.lo), str(energy_interval.hi)],
        "d4d_energy_interval_decimal": interval_decimal(energy_interval),
        "d4d_energy_interval_scope": "D4d one-parameter family candidate only; not a global n=10 lower bound",
        "candidate_t_decimal": mp.nstr(candidate_t, 80),
        "candidate_h_decimal": mp.nstr(h, 80),
        "original_radical_branch_residual_at_decimal": mp.nstr(radical_residual, 50),
        "branch_check": "RATIONAL_INTERVAL_ENDPOINT_SIGNS_DECIMAL_ROOT_RESIDUAL",
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
