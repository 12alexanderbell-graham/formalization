#!/usr/bin/env bash
# Run `Claims.paramClosureFaults` (copied from a Claims.lean, or from the scratch rule file) on a body file:
# controls or the bench (run 2026-11-26T0828Z, part 3). Usage: run_pclosure.sh <rule source> <body> (after lake build Checked)
set -euo pipefail
root="$(git rev-parse --show-toplevel)"; cd "$root"
src="$1"; body="$2"
out="$(mktemp -d)/PBench.lean"
{
  echo "import Checked"
  echo "open Lean Meta Elab Command"
  echo "namespace Claims"
  awk '/^\/-- Value of a closed real numeral/{p=1} p{print} p&&/^  return bad$/{exit}' "$src"
  echo "end Claims"
  cat "$body"
} > "$out"
grep -q "def paramClosureFaults" "$out" || { echo "paramClosureFaults not found in $src" >&2; exit 2; }
lake env lean "$out" 2>&1 | grep -v "^warning" | sed 's/^[^:]*PBench.lean:/PBench.lean:/'
