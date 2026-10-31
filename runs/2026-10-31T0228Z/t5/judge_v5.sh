#!/bin/bash
# T5 judge v5 (run 0228Z): the checks on main as CI runs them, incl. `lake build Work` (the CI work
# job and the axiom-audit step build Work; the 0028Z judge omitted it) and the certified-number check.
# Works in a second worktree W (default /home/claude/fz2) at BASE; the main tree is untouched.
# Author model as in 0028Z: the author relocks frozen.txt (TRUST_RELOCK=1) and commits; a LEDGER
# line is added only if the defect itself adds one. TRUST_MAP.md as the defect leaves it.
# Usage: judge_v5.sh <defect dir with apply.py | NONE> <out file>
set -u
W=${W:-/home/claude/fz2}; D=$1; OUT=$2
export PATH=$HOME/.elan/bin:$PATH
cd $W
BASE=$(git rev-parse HEAD)
{
echo "defect: $D  base: $BASE"; date -u +%T
if [ "$D" != NONE ]; then python3 $D/apply.py $W || echo "RESULT APPLY_FAILED"; fi
echo "--- changed files"; git status --porcelain
cp TRUST_MAP.md /tmp/v5_map_defect.md
echo "--- build Checked Work"
if timeout 2400 lake build Checked Work > /tmp/v5_build.log 2>&1; then echo "build: PASS"; B=0; else echo "build: FAIL"; B=1; grep -E "error" /tmp/v5_build.log | head -n 12; fi
echo "--- forbidden tokens"
if grep -rnE '\b(sorry|admit|axiom|native_decide|implemented_by|debug\.skipKernelTC)\b' Checked Checked.lean; then T=1; echo "tokens: FAIL"; else T=0; echo "tokens: PASS"; fi
S=1; M=1; N=1; R=1
if [ $B = 0 ]; then
  echo "--- trust step (author relocks)"
  if TRUST_RELOCK=1 timeout 900 lake env lean scripts/trust/StatementDeps.lean > /tmp/v5_sd.log 2>&1; then S=0; echo "trust: PASS"; else echo "trust: FAIL"; grep -v "^ " /tmp/v5_sd.log | grep -iE "error|rests on|witness|pin |never used|cite|imports|FROZEN|registered|RoundsTo" | head -n 15; fi
  if cmp -s TRUST_MAP.md /tmp/v5_map_defect.md; then M=0; echo "map: PASS"; else echo "map: FAIL (committed TRUST_MAP.md is stale)"; fi
  cp /tmp/v5_map_defect.md TRUST_MAP.md
  echo "--- certified numbers"
  python3 scripts/trust/check_numbers.py && N=0
  git add -A >/dev/null; git -c user.email=j@x -c user.name=judge commit -qm "defect" >/dev/null 2>&1
  echo "--- frozen registry + certified-number diff vs base"
  python3 scripts/trust/check_relock.py $BASE && python3 scripts/trust/check_numbers.py --base $BASE && R=0
fi
if [ $B = 0 ] && [ $T = 0 ] && [ $S = 0 ] && [ $M = 0 ] && [ $N = 0 ] && [ $R = 0 ]; then echo "RESULT V5 ACCEPTED"; else echo "RESULT V5 REJECTED build=$B tokens=$T trust=$S map=$M numbers=$N relock=$R"; fi
date -u +%T
} > $OUT 2>&1
git reset -q --hard $BASE; git clean -fdq -- Checked Work scripts runs
tail -n 2 $OUT
