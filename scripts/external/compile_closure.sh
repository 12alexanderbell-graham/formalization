#!/usr/bin/env bash
# Compile a target-O closure locally against the frozen challenge, with THIS repository's Mathlib
# (run 2026-11-27T1628Z, annex LIV: runs reinvented this recipe each time; ~10 min lost per run).
#
# Usage: scripts/external/compile_closure.sh <outside lean dir> <scratch dir> <Readings.mod=path> [Challenge ...] -- <closure.lean> [<closure2.lean> ...]
#   e.g. scripts/external/compile_closure.sh /home/claude/ext/oai/lean /tmp/x \
#          Readings.turing=runs/.../closure/Readings.lean DegreeRigidity -- runs/.../Closure.lean
# Each challenge `ComparatorChallenges/<Name>.lean` is copied from the outside dir and compiled to an .olean in the
# scratch dir, the readings file likewise under its module name; the closures are then elaborated with the scratch
# dir on LEAN_PATH (a closure named Closure/X.lean in the scratch dir may be imported by later closures as
# Closure.X: pass it as Closure.X=path before `--`). Prints errors and `#print axioms` lines only.
# Advisory, not a judge: the binding check is the replay at the outside project's own pin (external.yml).
set -euo pipefail
root="$(git rev-parse --show-toplevel)"; cd "$root"
export PATH="$HOME/.elan/bin:$PATH"
OUT=$1; S=$2; shift 2
mkdir -p "$S/ComparatorChallenges"
LP=$(lake env printenv LEAN_PATH)
build() { # module file
  local mod=$1 file=$2 rel=${1//.//}.lean
  mkdir -p "$S/$(dirname "$rel")"; cp "$file" "$S/$rel"
  LEAN_PATH="$S:$LP" lean --root="$S" -o "$S/${mod//.//}.olean" "$S/$rel" 2>&1 | grep -v "declaration uses .sorry" || true
}
while [ $# -gt 0 ] && [ "$1" != "--" ]; do
  case "$1" in
    *=*) build "${1%%=*}" "${1#*=}" ;;
    *) build "ComparatorChallenges.$1" "$OUT/ComparatorChallenges/$1.lean" ;;
  esac
  shift
done
[ "${1:-}" = "--" ] && shift
for f in "$@"; do
  echo "== $f"
  cp "$f" "$S/_check.lean"
  LEAN_PATH="$S:$LP" lean --root="$S" "$S/_check.lean" 2>&1 | grep -E "error|depends on axioms|^  |^⊢" | head -80 || true
done
