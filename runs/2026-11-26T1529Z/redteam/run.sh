#!/bin/bash
# usage: run.sh <variant> [EXTRA...]
v=$1; shift
W=${WORK:?set WORK to a replay project of S-egyptian}
cd "$(dirname "$0")"
start=$(date +%s)
LC_SKIP=1 NANODA=0 EXTRA="$*" bash "${REPO:-../../..}"/scripts/external/replay.sh "$v" "$W" OAI.NumberTheory.ShortEgyptian.Main ComparatorChallenges.ShortEgyptianFractions OAI.ShortEgyptian.main > "log_$v.txt" 2>&1
rc=$?
echo "$v rc=$rc $(( $(date +%s) - start ))s"
grep -v '^  •' "log_$v.txt" | grep -E "FAIL|PASSED|COMPARE|differ|MISSING|axioms|BLOCKER|error" | head -12
