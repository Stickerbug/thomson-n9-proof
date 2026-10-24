#!/usr/bin/env python3
"""Deterministic numerical proposal generator for the ten-point Thomson problem.

This is a discovery tool only.  Its output is deliberately labelled as a
proposal: floating-point coordinates do not establish exact stationarity,
global minimality, or a Lean certificate.
"""
from __future__ import annotations

import hashlib
import json
import platform
import sys
import time
from pathlib import Path

import numpy as np
import scipy
from scipy.optimize import minimize

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "n10_numerical_candidate_proposal_2026-10-24.json"
N = 10
SEED = 20261024
STARTS = 32


def unpack(x: np.ndarray) -> np.ndarray:
    theta, phi = x[:N], x[N:]
    return np.c_[np.sin(theta) * np.cos(phi),
                 np.sin(theta) * np.sin(phi), np.cos(theta)]


def energy(x: np.ndarray) -> float:
    p = unpack(x)
    dot = p @ p.T
    i, j = np.triu_indices(N, 1)
    return float(np.sum(1.0 / np.sqrt(2.0 - 2.0 * dot[i, j])))


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    started = time.monotonic()
    rng = np.random.default_rng(SEED)
    runs = []
    best = None
    for k in range(STARTS):
        p = rng.normal(size=(N, 3))
        p /= np.linalg.norm(p, axis=1)[:, None]
        x0 = np.r_[np.arccos(np.clip(p[:, 2], -1.0, 1.0)),
                   np.arctan2(p[:, 1], p[:, 0])]
        result = minimize(energy, x0, method="L-BFGS-B",
                          options={"maxiter": 1500, "ftol": 1e-13,
                                   "gtol": 1e-9, "maxls": 50})
        row = {"start": k, "energy": float(result.fun),
               "success": bool(result.success), "iterations": int(result.nit),
               "message": str(result.message)}
        runs.append(row)
        if best is None or result.fun < best.fun:
            best = result
    assert best is not None
    points = unpack(best.x)
    dot = points @ points.T
    i, j = np.triu_indices(N, 1)
    distances = np.sqrt(2.0 - 2.0 * dot[i, j])
    anti = np.abs(points @ points.T + 1.0)
    anti[np.diag_indices(N)] = np.inf
    proposal = {
        "status": "NUMERICAL_CANDIDATE_PROPOSAL_ONLY",
        "scope": "ten-point Thomson candidate discovery; no exactification, no global-minimum claim, no Lean theorem",
        "instance_n": N,
        "energy_convention": "sum over unordered pairs 1/||x_i-x_j||",
        "candidate_energy_float64": float(best.fun),
        "candidate_points_float64": points.tolist(),
        "min_pair_distance": float(np.min(distances)),
        "max_pair_distance": float(np.max(distances)),
        "closest_antipodal_pair_error": float(np.min(anti)),
        "optimizer": {"method": "L-BFGS-B", "seed": SEED,
                      "starts": STARTS, "maxiter": 1500,
                      "scipy": scipy.__version__, "numpy": np.__version__},
        "reproducibility": {"python": sys.version.split()[0],
                            "platform": platform.platform(),
                            "source_sha256": sha256(Path(__file__))},
        "runs": runs,
        "elapsed_seconds": time.monotonic() - started,
        "next_gate": "exact candidate/model/contact certificate before n10_discovery can leave UNKNOWN",
    }
    OUT.write_text(json.dumps(proposal, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({k: proposal[k] for k in
                      ("status", "candidate_energy_float64", "min_pair_distance",
                       "closest_antipodal_pair_error", "elapsed_seconds")},
                     ensure_ascii=False))


if __name__ == "__main__":
    main()
