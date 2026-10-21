#!/usr/bin/env python3
"""Emit Lean leaf-certificate skeletons from the exact-arithmetic certificate data.

Reads sharp_root_inputs.json (the frozen interval enclosures) and writes Lean
stubs of the form `def cert_<label> : LocalCert` for the 12 local classes.
Numeric coefficients are filled in a later pass from the Bernstein data.
"""
import json, sys
SRC = "../d10_sharpconvex_exact2026_coefficients.json"
data = json.load(open(SRC))
centers = data.get("local_centers", [])
print("local_centers:", len(centers))
for c in centers:
    print(" ", c.get("label"), c.get("kind"))
