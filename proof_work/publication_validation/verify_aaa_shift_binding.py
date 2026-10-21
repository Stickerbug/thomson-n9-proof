#!/usr/bin/env python3
"""Exact staged-shift containment check for the AAA H00 coefficient binding.

This is an independent numeric check of the *formal* three-axis algorithm in
`SparseTranslation.lean`, not the generator's rounded `Box` implementation.
It reads the archived source intervals and center box, shifts them in the order
0,1,2 using exact rational interval arithmetic, and checks that every staged
target interval is contained in the archived `shifted_polynomial` interval.

Passing this check means the formal interval algorithm is numerically strong
enough for the archived coefficients. It is not a Lean proof and does not
identify the true residual coefficients.
"""
from __future__ import annotations

import json
from fractions import Fraction as F
from math import comb
from pathlib import Path
import sys

PV = Path(__file__).resolve().parent


def parse_interval(pair) -> tuple[F, F]:
    lo, hi = pair
    return F(lo), F(hi)


def imul(a: tuple[F, F], b: tuple[F, F]) -> tuple[F, F]:
    x, y = a
    u, v = b
    vals = (x * u, x * v, y * u, y * v)
    return min(vals), max(vals)


def iadd(a: tuple[F, F], b: tuple[F, F]) -> tuple[F, F]:
    return a[0] + b[0], a[1] + b[1]


def ipow(a: tuple[F, F], n: int) -> tuple[F, F]:
    r = (F(1), F(1))
    for _ in range(n):
        r = imul(r, a)
    return r


def shift_axis(poly, center_powers, axis: int):
    targets: list[tuple[int, int, int]] = []
    seen: set[tuple[int, int, int]] = set()
    for e, _ in poly:
        for kk in range(e[axis] + 1):
            t = list(e)
            t[axis] = kk
            t = tuple(t)
            if t not in seen:
                seen.add(t)
                targets.append(t)
    out = []
    for k in targets:
        total = (F(0), F(0))
        for e, interval in poly:
            if any(e[j] != k[j] for j in range(3) if j != axis):
                continue
            if k[axis] > e[axis]:
                continue
            term = imul(interval, (F(comb(e[axis], k[axis])),) * 2)
            total = iadd(total, imul(term, center_powers[e[axis] - k[axis]]))
        out.append((k, total))
    return out


def main() -> int:
    root = PV.parent.parent
    hermite = json.loads((PV / "independent_hermite_RH_result.json").read_text())
    aaa = json.loads((PV / "independent_local_00_AAA.json").read_text())
    source = [(tuple(e), parse_interval(i)) for e, i in hermite["R_coefficients"]]
    archived = {tuple(e): parse_interval(i) for e, i in aaa["shifted_polynomial"]}
    centers = [parse_interval(i) for i in aaa["new_center_intervals"]]
    if len(source) != 807:
        print(f"AAA_SHIFT_BINDING_FAIL: source count {len(source)} != 807")
        return 1
    if len(archived) != 807:
        print(f"AAA_SHIFT_BINDING_FAIL: archived count {len(archived)} != 807")
        return 1
    max_degree = max(e[i] for e, _ in source for i in range(3))
    powers = [
        [ipow(centers[i], n) for n in range(max_degree + 1)]
        for i in range(3)
    ]
    poly = source
    for axis in range(3):
        poly = shift_axis(poly, powers[axis], axis)
    got = {k: interval for k, interval in poly}
    missing = sorted(set(archived) - set(got))
    extra = sorted(set(got) - set(archived))
    bad = []
    for k, interval in got.items():
        q = archived[k]
        if not (q[0] <= interval[0] and interval[1] <= q[1]):
            bad.append((k, interval, q))
    print(f"AAA_SHIFT_BINDING_TARGETS {len(got)}")
    print(f"AAA_SHIFT_BINDING_MISSING {len(missing)}")
    print(f"AAA_SHIFT_BINDING_EXTRA {len(extra)}")
    print(f"AAA_SHIFT_BINDING_NOT_CONTAINED {len(bad)}")
    if missing or extra or bad:
        for item in bad[:3]:
            print("BAD", item)
        print("AAA_SHIFT_BINDING_FAIL")
        return 1
    print("AAA_SHIFT_BINDING_PASS: 807 targets, 807 contained")
    return 0


if __name__ == "__main__":
    sys.exit(main())
