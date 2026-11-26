#!/usr/bin/env bash
# Run the page's closure rule (`Claims.closureFaults`, copied verbatim from scripts/trust/Claims.lean at run time)
# on the bench of honest closures `runs/2026-11-26T0228Z/t5/bench_body.lean` (run 2026-11-26T0228Z, part 3).
# Usage: runs/2026-11-26T0228Z/scripts/bench_closure.sh [Claims.lean] [body]   (after lake build Checked)
set -euo pipefail
root="$(git rev-parse --show-toplevel)"; cd "$root"
claims="${1:-scripts/trust/Claims.lean}"
body="${2:-runs/2026-11-26T0228Z/t5/bench_body.lean}"
out="$(mktemp -d)/Bench.lean"
{
  echo "import Checked"
  echo "open Lean Meta Elab Command"
  echo "namespace Claims"
  # isCheckedConst and every helper up to the end of closureFaults (verbatim)
  awk '/^def isCheckedConst/{p=1} p{print} p&&/^  return bad$/{exit}' "$claims"
  echo "end Claims"
  cat "$body"
} > "$out"
grep -q "def closureFaults" "$out" || { echo "closureFaults not found in $claims" >&2; exit 2; }
lake env lean "$out" 2>&1 | grep -v "^warning" | sed 's/^[^:]*Bench.lean:/Bench.lean:/'
