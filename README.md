# Thomson n=9 — locally verified proof candidate

This repository contains the Lean formalization, exact-arithmetic checks, status documents and the canonical review bundle for the Thomson n=9 program.

**Status: locally verified proof candidate, not a solved theorem and not externally reviewed.**

The canonical locally verified configuration is:

- 644 `#print axioms` audits, 115-module closure;
- only `propext`, `Classical.choice`, `Quot.sound`;
- unified verifier status `LOCAL_LEAN_COMPILER_AXIOMS_AND_KERNEL_PASS`;
- 279/807 archived sparse-Hessian coefficient targets have conditional interval certificates;
- canonical bundle `proof_work/THOMSON_N9_REVIEW_BUNDLE.zip`, 304 entries, 16,641,132 bytes, SHA-256 `7d99da9b3c542ca84b14a793875ab6ad13354d80dd61717f5a3a755247d0cac9`.

## What is included

- `proof_work/publication_validation/formal/` — Lean sources and build scripts;
- `proof_work/publication_validation/` — exact checkers, verification reports, status docs and the review bundle;
- `proof_work/` — certificates, independent checks and research notes.

## What is excluded

The following are reproducible or too large for a normal Git repository:

- `.lake/` build directories, Lean toolchain and Python wheels;
- large frontier JSON files above GitHub's 100 MB limit;
- old review-bundle archives.

The canonical bundle is included; large omitted data can be attached to a GitHub Release if needed.

## Verification

The verifier is `proof_work/publication_validation/verify_local_lean.py`. It rebuilds or adopts the Lean artifacts, checks the 644 axiom directives, scans for banned tokens, and runs `leanchecker` on `ThomsonNine.LocalVerification`.

## Remaining trust gaps

The certificates are conditional: the AAA theorem assumes the coefficient family lies in archived `coefficientInterval` and the point lies in `relativeBox`. The true residual/shifted-coefficient binding, the other 11 classes, 45 contact equations, rank-33/W compatibility, the 68,063-leaf coverage instantiation and the final `ThomsonNineClaim` remain unformalized.

## Transfer

For a complete continuation brief, see `HANDOFF_TO_NEXT_AI_zh.md` and `HANDOFF_STATE.json`.
