#!/bin/bash
# Direct, sequential Lean build; preserve the existing .lake dependency cache.
set -euo pipefail
P="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$P"
if [ -n "${LEAN_BIN_DIR:-}" ]; then
  export PATH="$LEAN_BIN_DIR:$PATH"
elif ! command -v lean >/dev/null 2>&1; then
  case "$(uname -m)" in
    aarch64) archive=lean-4.34.1-linux_aarch64 ;;
    *) archive=lean-4.34.1-linux ;;
  esac
  export PATH="$P/../toolchain/$archive/bin:$PATH"
fi
export LEAN_PATH="$P/.lake/build/lib/lean:$P/.lake/packages/mathlib/.lake/build/lib/lean"
for package in aesop batteries Qq plausible importGraph proofwidgets LeanSearchClient Cli; do
  export LEAN_PATH="$LEAN_PATH:$P/.lake/pinned_sources/$package/.lake/build/lib/lean"
done
OUT="$P/.lake/build/lib/lean"
mkdir -p "$OUT/ThomsonNine"
for m in "$@"; do
  candidate="${m//.//}"
  if [ -f "$candidate.lean" ]; then rel="$candidate"; else rel="ThomsonNine/$candidate"; fi
  mkdir -p "$(dirname "$OUT/$rel")"
  echo "START $m $(date -u +%FT%TZ)"
  lean -o "$OUT/$rel.olean" -i "$OUT/$rel.ilean" "$rel.lean"
  echo "PASS $m $(date -u +%FT%TZ)"
done
