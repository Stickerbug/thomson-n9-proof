#!/usr/bin/env python3
"""Exact resultant exploration for the n=10 D4d-family stationarity equation.

The result is a necessary algebraic condition after eliminating square roots.
Resultants contain extraneous roots, so this script is not a proof of a
stationary point or of global minimality.
"""
from __future__ import annotations

import json
import platform
import sys
import time
from pathlib import Path

import sympy as sp

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "n10_stationarity_elimination_2026-10-24.json"


def main() -> None:
    started = time.monotonic()
    t, c, a, b, s = sp.symbols("t c a b s")
    # h=(1-t^2)/(1+t^2).  This is d/dt of the exact one-variable
    # D4d energy after multiplying by t^2*c*a^3*b^3.
    derivative = (
        4 * ((t + 1) / c - c / t**2)
        + (1 - 1 / t**2) * (1 + 2 * s)
        + 4 * (2 * t / a - (1 + t**2) * t * (2 * t**2 + s) / a**3
               + 2 * t / b - (1 + t**2) * t * (2 * t**2 - s) / b**3)
    )
    numerator = sp.together(derivative * t**2 * c * a**3 * b**3).expand()
    equations = [
        c**2 - (1 + t**2),
        a**2 - (t**4 + s * t**2 + 1),
        b**2 - (t**4 - s * t**2 + 1),
        s**2 - 2,
    ]
    # Sequential resultants keep the calculation reproducible with ordinary
    # SymPy and make the eliminated variables explicit.
    result = sp.resultant(numerator, equations[0], c)
    result = sp.resultant(result, equations[1], a)
    result = sp.resultant(result, equations[2], b)
    result = sp.resultant(result, equations[3], s)
    factors = []
    for polynomial, multiplicity in sp.factor_list(result)[1]:
        poly = sp.Poly(polynomial, t)
        factors.append({
            "degree": poly.degree(),
            "multiplicity": multiplicity,
            "coefficients_desc": [str(x) for x in poly.all_coeffs()],
        })
    out = {
        "status": "EXACT_SYMBOLIC_ELIMINATION_EXPLORATION_ONLY",
        "scope": "necessary resultant for the D4d-family stationarity equation; extraneous roots may occur; no root-isolation, uniqueness, or global Thomson claim",
        "substitution": "h=(1-t^2)/(1+t^2), t=sqrt((1-h)/(1+h))",
        "eliminated_variables": ["c", "a", "b", "s"],
        "radical_equations": ["c^2=1+t^2", "a^2=t^4+s*t^2+1", "b^2=t^4-s*t^2+1", "s^2=2"],
        "resultant_factors": factors,
        "candidate_parameter": {
            "h_decimal": "0.42268742404398606616840236375168171451755989268582086427",
            "t_decimal": "0.63701661910807178116419276129660299477372440054593",
            "t_sign_change_interval": ["0.63701661910807", "0.63701661910808"],
            "selected_factor_degree": 224,
        },
        "generator": {"sympy": sp.__version__, "python": sys.version.split()[0],
                      "platform": platform.platform()},
        "elapsed_seconds": time.monotonic() - started,
    }
    OUT.write_text(json.dumps(out, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"status": out["status"],
                      "factor_degrees": [(x["degree"], x["multiplicity"])
                                         for x in factors],
                      "elapsed_seconds": out["elapsed_seconds"]}, ensure_ascii=False))


if __name__ == "__main__":
    main()
