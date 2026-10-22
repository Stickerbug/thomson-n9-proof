# Reproduce the complete frozen Lean theorem

Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. Other pins are in `lake-manifest.original_git.json`. Preserve `.lake` and restore architecture-matching dependency caches when needed.

```bash
cd /workspace/thomson-n9-proof
export LEAN_BIN_DIR=/path/to/lean-4.34.1/bin
python3 -B proof_work/publication_validation/verify_local_lean.py
```

The verifier discovers both ThomsonNine modules and the original-name proof modules explicitly owned by `../packed_coverage_manifest.json`, compiles dependencies in order, then checks root, LocalVerification and Axioms. It rejects unregistered local imports and proof escapes, checks all source templates and input hashes, audits 1507 distinct conclusions, and replays the entire 2390-module closure through `leanchecker --fresh ThomsonNine.LocalVerification`.

The final theorem is `ThomsonNine.thomsonNineClaim_proved : ThomsonNine.ThomsonNineClaim`, in `MainCoverage/Final.lean`. Statement.lean is unchanged. Current full fresh replay PASS: 13228.2 seconds. This is Lean's own kernel, not an external independent verifier.

After a matching PASS, `--reuse-local-build` checks all source/artifact hashes. `--adopt-build` explicitly adopts existing artifacts after mtime/hash checks and still runs complete fresh validation. Exact existing artifacts were adopted in this checkpoint, preserving original module identities; no from-scratch compilation is claimed.

`build_direct.sh MainCoverage.Final` or `build_direct.sh ThomsonNine` builds a selected module from this directory. Use the Python verifier for a clean dependency-ordered rebuild. Historical `ThomsonNine/Construction` aliases are kept for reproducibility and are not imported alongside the current original-name modules.

After PASS, `python3 proof_work/publication_validation/build_review_bundle.py` builds the source review archive and refuses stale reports, mismatched hashes, or incomplete fresh coverage. See `../GLOBAL_THEOREM_2026-10-22_zh.md` for mathematical scope and exact evidence.
