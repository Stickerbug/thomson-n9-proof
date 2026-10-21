# Large data and excluded artifacts

GitHub release: https://github.com/Stickerbug/thomson-n9-proof/releases/tag/data-2026-10-21

## Direct asset

- `nonsharp_d10_root25_759925_v9_depth300_frontier.json` (56,035,759 bytes)
  SHA-256: see the release asset `SHA256SUMS` (or compute it locally).

## Split asset

`nonsharp_d10_root25_759925_v9_depth1000_frontier.json` is split into six parts (GitHub's asset uploader repeatedly aborted on the 45 MB third part):

```
frontier_depth1000.part00   47185920
frontier_depth1000.part01   47185920
frontier_depth1000.part02   47185920
frontier_depth1000.part030  24117248
frontier_depth1000.part031  23068672
frontier_depth1000.part04    2871041
```

Reassemble:

```bash
cat frontier_depth1000.part00 frontier_depth1000.part01 frontier_depth1000.part02 \
    frontier_depth1000.part030 frontier_depth1000.part031 frontier_depth1000.part04 \
    > nonsharp_d10_root25_759925_v9_depth1000_frontier.json
sha256sum -c <<'SUM'
b17700cd03efa7358a02f7786f64007b7eaed38b965790f90c4cc35003daf8d1  nonsharp_d10_root25_759925_v9_depth1000_frontier.json
SUM
```

## Not uploaded

- `formal/.lake/` (about 8.0 GB) and `publication_validation/toolchain/` (about 4.1 GB): reproducible Lean build artifacts/toolchain, not source.
- `python_deps/` and `.venv/`: Python wheels/environment.
- Old review-bundle archives; the canonical bundle is committed.

The canonical review bundle is `proof_work/THOMSON_N9_REVIEW_BUNDLE.zip` (304 entries, 16,641,132 bytes, SHA-256 `7d99da9b3c542ca84b14a793875ab6ad13354d80dd61717f5a3a755247d0cac9`).
