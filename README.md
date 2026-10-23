# Thomson n=9 — frozen global theorem proved in Lean

`ThomsonNine.thomsonNineClaim_proved : ThomsonNine.ThomsonNineClaim` proves the unchanged frozen specification: the stated candidate at its unique stationary radius attains the global minimum among injective nine-point configurations on the unit sphere.

Compiler, axiom audit and one complete fresh Lean-kernel replay pass: **2390 modules, 1507 audits, 807/807 distinct coefficient targets**. The replay took 13228.2 seconds. Only `propext`, `Classical.choice` and `Quot.sound` occur in audited conclusions.

See the [complete proof and validation record](proof_work/publication_validation/GLOBAL_THEOREM_2026-10-22_zh.md), [frozen statement](proof_work/publication_validation/formal/ThomsonNine/Statement.lean), [final theorem](proof_work/publication_validation/formal/MainCoverage/Final.lean), and [verification report](proof_work/publication_validation/local_lean_verification.json).

For the n=7/n=8 comparison and publication checklist, see [publication readiness](proof_work/publication_validation/README_PUBLICATION_READINESS_2026-10-22_zh.md). The planned reusable-certificate direction is recorded in [the generic framework roadmap](proof_work/publication_validation/GENERIC_CERTIFICATE_FRAMEWORK_ROADMAP_zh.md).

The current manuscript draft is available as [PDF](paper/main.pdf), with its [LaTeX source](paper/main.tex), [compact submission package](paper/THOMSON_N9_MANUSCRIPT_SOURCE.zip), [build notes](paper/README.md), [Chinese submission guide](paper/SUBMISSION_GUIDE_zh.md), and [cover-letter template](paper/COVER_LETTER_TEMPLATE.md). The archived release is [GitHub n9-proof-2026-10-23](https://github.com/Stickerbug/thomson-n9-proof/releases/tag/n9-proof-2026-10-23), DOI [10.5281/zenodo.23573472](https://doi.org/10.5281/zenodo.23573472).

Lean's built-in `leanchecker --fresh` is not an external independent verifier. No external peer review is claimed. The frozen theorem does not assert congruence uniqueness of all minimizers.

To reproduce, use Lean 4.34.1 and pinned Mathlib, preserve `formal/.lake`, and run:

```bash
export LEAN_BIN_DIR=/path/to/lean-4.34.1/bin
python3 -B proof_work/publication_validation/verify_local_lean.py
```

A matching PASS stamp permits `--reuse-local-build`; explicit existing-build adoption uses `--adopt-build`. All modes run the complete fresh replay. Original module names preserve compiler-cache identity; their owned sources are registered in `packed_coverage_manifest.json`.

The canonical source review archive is `proof_work/THOMSON_N9_REVIEW_BUNDLE.zip`; its size and SHA-256 are in `HANDOFF_STATE.json`. Historical progress records remain available. The original coverage baseline was 272 distinct targets, then 279 after the first seven additions.
