#!/bin/bash
# T5 judge L (run 2026-11-05T2228Z; copied from runs/2026-11-05T1628Z/t5/judge_K.sh; adds check_provenance and an AFTER pass with this run's scripts): the CI checked job and trust steps, run on a tree with the given
# defects applied, in the worktree /home/claude/fz2 (detached at BASE, .lake/packages symlinked,
# .lake/build copied). Usage: judge_K.sh <label> <base> <redteam dir> d01 d02 ...
# Steps as in .github/workflows/lean.yml: build Checked, forbidden-token grep, trust step (author
# relock, as the red team was told the author relocks), numbers, prose, trusted defs, Claims.lean,
# check_claims, packet, then every --base diff after committing the defects (local commit only).
set -u
export PATH=$HOME/.elan/bin:$PATH
L=$1; BASE=$2; RT=$3; shift 3
OUT=/home/claude/judgeL_$L; mkdir -p $OUT
cd /home/claude/fz2
git reset -q --hard $BASE; git clean -qfd Checked scripts
for d in "$@"; do python3 $RT/$d/apply.py . > /dev/null && echo "applied $d" || echo "APPLY FAILED $d"; done
echo "== new files compile one by one $(date -u +%T)"
for f in $(git status --short | awk '/^\?\?/{print $2}' | grep '\.lean$'); do
  timeout 900 lake env lean $f > $OUT/compile_$(basename $f).log 2>&1 && echo "  ok $f" || { echo "  FAIL $f"; grep -m5 error $OUT/compile_$(basename $f).log; }
done
echo "== build $(date -u +%T)"
lake build Checked > $OUT/build.log 2>&1 && echo "build: PASS" || { echo "build: FAIL"; grep -m10 "error" $OUT/build.log; }
if grep -rnE '\b(sorry|admit|axiom|native_decide|implemented_by|debug\.skipKernelTC)\b' Checked Checked.lean; then echo "grep: FAIL"; else echo "grep: PASS"; fi
echo "== trust $(date -u +%T)"
TRUST_RELOCK=1 timeout 1200 lake env lean scripts/trust/StatementDeps.lean > $OUT/sd.log 2>&1 && echo "trust: PASS" || { echo "trust: FAIL"; grep -v "^    " $OUT/sd.log | grep -iE "error|fail|rests|witness|pin|unused|frozen|CLAIM|COMPOSITE|FORMULA|label|kind" | head -20; }
echo "--- numbers"; python3 scripts/trust/check_numbers.py 2>&1 | tail -4
echo "--- prose"; python3 scripts/trust/check_prose.py 2>&1 | tail -25
echo "--- trusted defs"; python3 scripts/trust/check_trusted_defs.py 2>&1 | tail -3
echo "--- claims $(date -u +%T)"; timeout 900 lake env lean scripts/trust/Claims.lean > $OUT/claims.log 2>&1; tail -3 $OUT/claims.log; python3 scripts/trust/check_claims.py 2>&1 | tail -5
echo "--- packet"; python3 validation/make_packet.py 2>&1 | tail -2
cp CLAIMS.md TRUST_MAP.md $OUT/
git add -A >/dev/null; git -c user.email=j@x -c user.name=judge commit -qm "defects $L" >/dev/null 2>&1
echo "--- base diffs vs $BASE"
for s in "check_relock.py $BASE" "check_numbers.py --base $BASE" "check_prose.py --base $BASE" "check_trusted_defs.py --base $BASE" "check_claims.py --base $BASE" "check_formulas.py --base $BASE"; do
  echo "  [$s]"; python3 scripts/trust/$s 2>&1 | tail -4 | sed 's/^/    /'
done
echo "== end $(date -u +%T)"
echo "== AFTER: this run's scripts (StatementDeps rules for agreements of propositions and inline CLAIM arithmetic; check_provenance) $(date -u +%T)"
NEW=/home/claude/formalization/scripts/trust
cp $NEW/StatementDeps.lean $NEW/check_provenance.py $NEW/gen_claim_readings.py $NEW/provenance_baseline.txt scripts/trust/
TRUST_RELOCK=1 timeout 1200 lake env lean scripts/trust/StatementDeps.lean > $OUT/sd_after.log 2>&1 && echo "trust after: PASS" || { echo "trust after: FAIL"; grep -v "^    " $OUT/sd_after.log | grep -iE "error|agreement|inline|CLAIM" | head -20; }
echo "  [check_provenance --base $BASE]"; python3 scripts/trust/check_provenance.py --base $BASE 2>&1 | tail -12 | sed 's/^/    /'
git checkout -q -- scripts/trust 2>/dev/null
echo "== end after $(date -u +%T)"
