#!/usr/bin/env python3
"""Fit the observed n=10 numerical proposal to a D4d one-parameter family.

The family is a pair of antipodal poles plus two staggered square rings.  This
only reduces candidate search to one variable; it is not a global proof.
"""
from __future__ import annotations

import json
import math
import platform
import sys
import time
from pathlib import Path

import numpy as np
import mpmath as mp
from scipy.optimize import minimize_scalar

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "n10_d4d_symmetric_family_2026-10-24.json"


def family_points(h: float) -> np.ndarray:
    r = math.sqrt(1.0 - h * h)
    lower = [(r * math.cos(k * math.pi / 2), r * math.sin(k * math.pi / 2), -h)
             for k in range(4)]
    upper = [(r * math.cos(math.pi / 4 + k * math.pi / 2),
              r * math.sin(math.pi / 4 + k * math.pi / 2), h)
             for k in range(4)]
    return np.array([(0.0, 0.0, 1.0), (0.0, 0.0, -1.0), *lower, *upper])


def energy(h: float) -> float:
    # Pair counts after reducing the D4d orbit types.
    return (0.5 + 8 / math.sqrt(2 - 2 * h) + 8 / math.sqrt(2 + 2 * h)
            + 8 / math.sqrt(2 - 2 * h * h) + 2 / math.sqrt(1 - h * h)
            + 8 / math.sqrt(2 + 2 * h * h - math.sqrt(2) * (1 - h * h))
            + 8 / math.sqrt(2 + 2 * h * h + math.sqrt(2) * (1 - h * h)))


def main() -> None:
    started = time.monotonic()
    result = minimize_scalar(energy, bounds=(0.2, 0.7), method="bounded",
                             options={"xatol": 1e-15, "maxiter": 1000})
    # Refine the scalar stationary point with high-precision differentiation;
    # the stored value is still only a numerical proposal.
    mp.mp.dps = 80
    def mp_energy(x):
        x = mp.mpf(x)
        return (mp.mpf("0.5") + 8 / mp.sqrt(2 - 2 * x) + 8 / mp.sqrt(2 + 2 * x)
                + 8 / mp.sqrt(2 - 2 * x * x) + 2 / mp.sqrt(1 - x * x)
                + 8 / mp.sqrt(2 + 2 * x * x - mp.sqrt(2) * (1 - x * x))
                + 8 / mp.sqrt(2 + 2 * x * x + mp.sqrt(2) * (1 - x * x)))
    h_mp = mp.findroot(lambda x: mp.diff(mp_energy, x), (mp.mpf("0.42"), mp.mpf("0.43")))
    h = float(h_mp)
    p = family_points(h)
    dots = p @ p.T
    i, j = np.triu_indices(10, 1)
    distances = np.sqrt(2 - 2 * dots[i, j])
    out = {
        "status": "SYMMETRIC_NUMERICAL_FAMILY_PROPOSAL_ONLY",
        "scope": "D4d one-parameter fit for n=10 discovery; no global-minimum or Lean claim",
        "parameter": "h",
        "parameter_interval": [0, 1],
        "h_float64": h,
        "h_high_precision_decimal": mp.nstr(h_mp, 70),
        "energy_float64": float(mp_energy(h_mp)),
        "family_definition": {
            "poles": "(0,0,1), (0,0,-1)",
            "lower_ring": "sqrt(1-h^2)*(cos(k*pi/2),sin(k*pi/2),0)+(0,0,-h), k=0..3",
            "upper_ring": "sqrt(1-h^2)*(cos(pi/4+k*pi/2),sin(pi/4+k*pi/2),0)+(0,0,h), k=0..3",
        },
        "energy_formula": "1/2 + 8/sqrt(2-2h) + 8/sqrt(2+2h) + 8/sqrt(2-2h^2) + 2/sqrt(1-h^2) + 8/sqrt(2+2h^2-sqrt(2)(1-h^2)) + 8/sqrt(2+2h^2+sqrt(2)(1-h^2))",
        "minimum_pair_distance": float(np.min(distances)),
        "optimizer": {"method": "scipy.optimize.minimize_scalar", "bounds": [0.2, 0.7],
                      "scipy": __import__("scipy").__version__},
        "candidate_points_float64": p.tolist(),
        "reproducibility": {"python": sys.version.split()[0], "platform": platform.platform()},
        "elapsed_seconds": time.monotonic() - started,
        "next_gate": "derive an exact algebraic stationarity certificate and prove the full ten-point global bound",
    }
    OUT.write_text(json.dumps(out, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({k: out[k] for k in ("status", "h_float64", "energy_float64", "elapsed_seconds")}, ensure_ascii=False))


if __name__ == "__main__":
    main()
