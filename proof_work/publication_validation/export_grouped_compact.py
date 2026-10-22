#!/usr/bin/env python3
"""Generate compact grouped certificates without changing their interfaces.

Use the existing generator for the interval expressions and theorem statements.
Reuse mem_mul instead of proving eight corner bounds for the exact same product.
Reduce closed exponent lookups by definitional equality before normalization,
so simp does not store repeated proofs through the 807-case exponent definition.
Every resulting theorem still requires ordinary Lean compilation and auditing.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile


PV = Path(__file__).resolve().parent


def compact_source(text, target, coefficients):
    """Change only proof bodies; callers must compile the result with Lean."""
    exponent = coefficients[target][0]
    sources = [(i, e) for i, (e, _) in enumerate(coefficients)
               if all(e[j] >= exponent[j] for j in range(3))]
    lines = text.splitlines(keepends=True)
    compact = []
    products = 0
    i = 0
    while i < len(lines):
        prefix = "    refine mem_mul_of_bounds "
        if lines[i].startswith(prefix):
            premises, goals = lines[i][len(prefix):].split(" ?_", 1)
            if goals.count("?_") != 7 or not lines[i + 1].startswith("      (simp only ["):
                raise RuntimeError("unexpected generic product-proof format")
            # The legacy t114 source stores three precomputed scalar products
            # as explicit rational endpoints, rather than definitions of mul.
            # Keep their numeric enclosure proofs; they are not definitionally
            # equal to the exact product operation.
            if premises.startswith("(mem_const "):
                compact.extend(lines[i:i + 2])
                i += 2
                continue
            compact.append("    exact ThomsonNine.Interval.RatInterval.mem_mul " + premises + "\n")
            products += 1
            i += 2
        else:
            compact.append(lines[i])
            i += 1
    text = "".join(compact)
    terms = []
    for index, source_exponent in sources:
        expression = f"(c .t{index:03d})"
        for axis in range(3):
            n, k = source_exponent[axis], exponent[axis]
            expression = f"({expression} * ((Nat.choose {n} {k} : ℝ) * a {axis} ^ {n - k}))"
        terms.append(expression)
    expression = terms[-1]
    for term in reversed(terms[:-1]):
        expression = f"{term} + ({expression})"
    old = "    simp [expandedCoefficient, shiftFactor, Nat.choose, exponents]\n    ring"
    if text.count(old) != 1:
        raise RuntimeError("unexpected generic gathered-proof format")
    new = ("    change (" + expression + ") = _\n"
           "    norm_num only [Nat.choose, Nat.cast_add, Nat.cast_mul, "
           "Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]\n    ring")
    text = text.replace(old, new)
    return text, products


def generate(target, namespace, coefficients, template=None):
    if template is not None:
        text = template.read_text()
        if not re.search(r'^namespace ThomsonNine\.' + re.escape(namespace) + r'\s*$', text, re.M):
            raise RuntimeError("legacy template namespace mismatch")
        return compact_source(text, target, coefficients)
    with tempfile.TemporaryDirectory(prefix="thomson-compact-") as temporary:
        original = Path(temporary) / "original.lean"
        subprocess.run([sys.executable, str(PV / "export_grouped_generic.py"),
                        str(target), str(original), namespace],
                       check=True, stdout=subprocess.PIPE, text=True)
        return compact_source(original.read_text(), target, coefficients)


def check_certificates(coefficients):
    expected = json.loads((PV / "local_lean_expected.json").read_text())["compact_grouped_modules"]
    manifest = json.loads((PV / "compact_grouped_manifest.json").read_text())
    entries = manifest["modules"]
    names = [e["module"] for e in entries]
    if len(names) != len(set(names)) or set(names) != set(expected):
        raise RuntimeError("compact module manifest differs from registered expectations")
    for entry in entries:
        template = PV / entry["template"] if entry.get("template") else None
        if template and hashlib.sha256(template.read_bytes()).hexdigest() != entry["baseline_source_sha256"]:
            raise RuntimeError("legacy template hash mismatch")
        text, products = generate(entry["target"], entry["namespace"], coefficients, template)
        source = PV / "formal" / Path(entry["module"].replace(".", "/")).with_suffix(".lean")
        if source.read_text() != text or hashlib.sha256(text.encode()).hexdigest() != entry["source_sha256"]:
            raise RuntimeError("compact source mismatch: " + entry["module"])
        if products != entry["reused_product_lemmas"]:
            raise RuntimeError("compact product count mismatch: " + entry["module"])
    print(json.dumps({"status": "COMPACT_REGENERATION_PASS", "modules": len(entries)}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("target", type=int, nargs="?")
    parser.add_argument("output", type=Path, nargs="?")
    parser.add_argument("namespace", nargs="?")
    parser.add_argument("--source", type=Path, help="preserve a legacy source's definitions and signatures")
    parser.add_argument("--check", action="store_true", help="regenerate all registered compact modules")
    args = parser.parse_args()
    coefficients = json.loads((PV / "independent_hermite_RH_result.json").read_text())["R_coefficients"]
    if args.check:
        check_certificates(coefficients)
        return
    target, output, namespace = args.target, args.output, args.namespace
    if target is None or output is None or namespace is None:
        parser.error("TARGET OUTPUT.lean NAMESPACE are required unless --check is used")
    if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", namespace):
        parser.error("namespace must be a simple Lean identifier")
    if not 0 <= target < len(coefficients):
        parser.error("target is out of range")
    text, products = generate(target, namespace, coefficients, args.source)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(text)
    print(json.dumps({"output": str(output), "target": target,
                      "reused_product_lemmas": products,
                      "status": "GENERATED_NOT_VERIFIED"}))


if __name__ == "__main__":
    main()
