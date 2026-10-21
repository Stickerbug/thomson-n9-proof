#!/bin/bash
# Direct Lean build (lake package resolution is unreliable in this container).
set -u
failed=0
P="/home/dsh/Thomson Problem/proof_work/publication_validation/formal"
cd "$P" || exit 1
export PATH="$P/../toolchain/lean-4.34.1-linux_aarch64/bin:$PATH"
export LEAN_PATH="$P/.lake/build/lib/lean:$P/.lake/packages/mathlib/.lake/build/lib/lean:$P/.lake/pinned_sources/aesop/.lake/build/lib/lean:$P/.lake/pinned_sources/batteries/.lake/build/lib/lean:$P/.lake/pinned_sources/Qq/.lake/build/lib/lean:$P/.lake/pinned_sources/plausible/.lake/build/lib/lean:$P/.lake/pinned_sources/importGraph/.lake/build/lib/lean:$P/.lake/pinned_sources/proofwidgets/.lake/build/lib/lean:$P/.lake/pinned_sources/LeanSearchClient/.lake/build/lib/lean:$P/.lake/pinned_sources/Cli/.lake/build/lib/lean"
OUT="$P/.lake/build/lib/lean/ThomsonNine"
mkdir -p "$OUT"
for m in "$@"; do
  echo "=== $(date +%H:%M:%S) building $m ==="
  if lean -o "$OUT/$m.olean" -i "$OUT/$m.ilean" "ThomsonNine/$m.lean" 2>&1; then
    echo "=== OK $m ==="
  else
    echo "=== FAIL $m ==="
    failed=1
  fi
done
echo "=== ALL DONE $(date +%H:%M:%S) ==="
exit "$failed"
