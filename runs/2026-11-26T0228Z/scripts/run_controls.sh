#!/usr/bin/env bash
# Run the closure controls of scripts/trust/Claims.lean against the closureFaults of a given Claims.lean
# (run 2026-11-26T0228Z): usage run_controls.sh <Claims.lean with the rule> [<Claims.lean with the controls>]
set -euo pipefail
root="$(git rev-parse --show-toplevel)"; cd "$root"
rule="$1"; ctl="${2:-scripts/trust/Claims.lean}"
out="$(mktemp -d)/Ctl.lean"
{
  echo "import Checked"
  echo "open Lean Meta Elab Command"
  echo "namespace Claims"
  awk '/^def isCheckedConst/{p=1} p{print} p&&/^  return bad$/{exit}' "$rule"
  echo "end Claims"
  awk '/^\/-! Planted controls of/{p=1} p&&/^set_option maxHeartbeats 0 in$/{exit} p{print}' "$ctl" | sed '$d'
} > "$out"
lake env lean "$out" 2>&1 | grep -v "^warning" | grep -v "linter\|Note:\|^$" | sed 's/^[^:]*Ctl.lean:/Ctl.lean:/' || true
echo "controls exit done"
