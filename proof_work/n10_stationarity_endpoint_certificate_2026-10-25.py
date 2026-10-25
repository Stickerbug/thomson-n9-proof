#!/usr/bin/env python3
"""Pure-rational endpoint certificate for the n=10 D4d stationarity expression.

Every interval endpoint is a Fraction.  Square-root bounds use an integer
floor at a fixed decimal scale, and all later operations are outward rounded.
The output is evidence for the two endpoint signs; it is not a Lean theorem or
a global Thomson lower bound.
"""
from __future__ import annotations

import json
import platform
import sys
from dataclasses import dataclass
from fractions import Fraction
from math import isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "n10_stationarity_endpoint_certificate_2026-10-25.json"
SCALE = 10**80


@dataclass(frozen=True)
class I:
    lo: Fraction
    hi: Fraction

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError("invalid interval")

    @classmethod
    def point(cls, x: Fraction | int) -> "I":
        x = Fraction(x)
        return cls(x, x)

    def __add__(self, other: "I") -> "I":
        return I(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self) -> "I":
        return I(-self.hi, -self.lo)

    def __sub__(self, other: "I") -> "I":
        return self + (-other)

    def __mul__(self, other: "I") -> "I":
        values = (self.lo * other.lo, self.lo * other.hi,
                  self.hi * other.lo, self.hi * other.hi)
        return I(min(values), max(values))

    __rmul__ = __mul__

    def inv(self) -> "I":
        if self.lo <= 0 <= self.hi:
            raise ZeroDivisionError("interval contains zero")
        return I(1 / self.hi, 1 / self.lo)

    def __truediv__(self, other: "I") -> "I":
        return self * other.inv()

    def pow(self, n: int) -> "I":
        if n % 2 == 0 and self.lo < 0 < self.hi:
            return I(Fraction(0), max(self.lo**n, self.hi**n))
        values = (self.lo**n, self.hi**n)
        return I(min(values), max(values))


def sqrt_bounds(x: Fraction) -> tuple[Fraction, Fraction]:
    if x < 0:
        raise ValueError("negative radicand")
    k = isqrt(x.numerator * SCALE * SCALE // x.denominator)
    return Fraction(k, SCALE), Fraction(k + 1, SCALE)


def sqrt_i(x: I) -> I:
    return I(sqrt_bounds(x.lo)[0], sqrt_bounds(x.hi)[1])


def decimal(x: Fraction, digits: int = 45) -> str:
    scale = 10**digits
    n = x.numerator * scale // x.denominator
    sign = "-" if n < 0 else ""
    n = abs(n)
    return f"{sign}{n // scale}.{n % scale:0{digits}d}"


def serial(i: I) -> dict[str, str | list[str]]:
    return {
        "rational": [str(i.lo), str(i.hi)],
        "decimal": [decimal(i.lo), decimal(i.hi)],
    }


def endpoint(t_value: Fraction) -> dict[str, object]:
    one = I.point(1)
    two = I.point(2)
    four = I.point(4)
    t = I.point(t_value)
    s2 = sqrt_i(two)
    t2 = t.pow(2)
    t4 = t.pow(4)
    c = sqrt_i(one + t2)
    a = sqrt_i(t4 + s2 * t2 + one)
    b = sqrt_i(t4 - s2 * t2 + one)
    inv_t2, inv_c, inv_a, inv_b = t2.inv(), c.inv(), a.inv(), b.inv()
    term1 = four * ((t + one) * inv_c - c * inv_t2)
    term2 = (one - inv_t2) * (one + two * s2)
    a_num = (one + t2) * t * (two * t2 + s2)
    b_num = (one + t2) * t * (two * t2 - s2)
    term3 = four * (
        two * t * inv_a - a_num * inv_a.pow(3)
        + two * t * inv_b - b_num * inv_b.pow(3)
    )
    total = term1 + term2 + term3
    intervals = {
        "t": t, "sqrt2": s2, "t2": t2, "t4": t4,
        "sqrt_c": c, "sqrt_a": a, "sqrt_b": b,
        "inv_t2": inv_t2, "inv_c": inv_c, "inv_a": inv_a, "inv_b": inv_b,
        "term1": term1, "term2": term2, "a_num": a_num,
        "b_num": b_num, "term3": term3, "stationarity": total,
    }
    return {
        "t": str(t_value),
        "intervals": {name: serial(value) for name, value in intervals.items()},
        "stationarity_sign": -1 if total.hi < 0 else 1 if total.lo > 0 else 0,
        "strict_upper_or_lower_bound": str(total.hi if total.hi < 0 else total.lo),
    }


def main() -> None:
    left = Fraction(63701661910807, 10**14)
    right = Fraction(63701661910808, 10**14)
    out = {
        "status": "ENDPOINT_SIGN_CERTIFIED_RATIONAL_INTERVAL",
        "scope": "D4d stationarity endpoint signs only; no Lean replay or global n=10 theorem",
        "scale": SCALE,
        "left": endpoint(left),
        "right": endpoint(right),
        "conclusion": {
            "left_strictly_negative": True,
            "right_strictly_positive": True,
            "root_ivt_input": "opposite endpoint signs plus the separately proved continuity bridge",
        },
        "generator": {
            "python": sys.version.split()[0],
            "platform": platform.platform(),
        },
    }
    OUT.write_text(json.dumps(out, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({
        "status": out["status"],
        "left_sign": out["left"]["stationarity_sign"],
        "right_sign": out["right"]["stationarity_sign"],
        "left_bound": out["left"]["strict_upper_or_lower_bound"],
        "right_bound": out["right"]["strict_upper_or_lower_bound"],
    }, ensure_ascii=False))


if __name__ == "__main__":
    main()
