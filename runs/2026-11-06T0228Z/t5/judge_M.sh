#!/bin/bash
# T5 judge M (run 2026-11-06T0228Z; from runs/2026-11-05T2228Z/t5/judge_L.sh). One tree, both measurements:
# fz2 is reset to BASE, this run's new check scripts (written blind to round M) are committed on top as S
# (old scripts unchanged in S), the defects are applied on top of S in the commit order they state
# (d03 stage 1 first), then the CI checked/trust steps run: BEFORE = the checks of main at BASE,
# AFTER = this run's four new scripts, --base S. Usage: judge_M.sh <label> <base> <redteam dir> d01 ...
set -u
export PATH=$HOME/.elan/bin:$PATH
L=$1; BASE=$2; RT=$3; shift 3
OUT=/home/claude/judgeM_$L; mkdir -p $OUT
NEW=/home/claude/formalization
cd /home/claude/fz2
git reset -q --hard $BASE; git clean -qfd Checked scripts runs
for f in check_literals.py check_source_names.py check_templates.py check_blind_route.py literal_baseline.txt literal_readings.txt source_names.txt source_names_baseline.txt claim_templates.txt; do cp $NEW/scripts/trust/$f scripts/trust/; done
git add -A >/dev/null; git -c user.email=j@x -c user.name=judge commit -qm "S: new checks" >/dev/null; S=$(git rev-parse HEAD)
STAGED=""
for d in "$@"; do grep -q -- "--stage" $RT/$d/apply.py && STAGED="$STAGED $d"; done
for d in $STAGED; do python3 $RT/$d/apply.py . --stage 1 > /dev/null && echo "applied $d stage 1" || echo "APPLY FAILED $d stage 1"; done
if [ -n "$STAGED" ]; then git add -A >/dev/null; git -c user.email=j@x -c user.name=judge commit -qm "defects $L stage 1" >/dev/null; fi
for d in "$@"; do
  if echo " $STAGED " | grep -q " $d "; then python3 $RT/$d/apply.py . --stage 2 > /dev/null && echo "applied $d stage 2" || echo "APPLY FAILED $d stage 2";
  else python3 $RT/$d/apply.py . > /dev/null && echo "applied $d" || echo "APPLY FAILED $d"; fi
done
echo "== new files compile one by one $(date -u +%T)"
for f in $(git status --short --untracked-files=all | awk '/^\?\?/{print $2}' | grep '\.lean$' | grep -v '^runs/'); do
  timeout 900 lake env lean $f > $OUT/compile_$(basename $f).log 2>&1 && echo "  ok $f" || { echo "  FAIL $f"; grep -m5 error $OUT/compile_$(basename $f).log; }
done
echo "== build $(date -u +%T)"
lake build Checked > $OUT/build.log 2>&1 && echo "build: PASS" || { echo "build: FAIL"; grep -m10 "error" $OUT/build.log; }
if grep -rnE '\b(sorry|admit|axiom|native_decide|implemented_by|debug\.skipKernelTC)\b' Checked Checked.lean; then echo "grep: FAIL"; else echo "grep: PASS"; fi
echo "== trust $(date -u +%T)"
TRUST_RELOCK=1 timeout 1500 lake env lean scripts/trust/StatementDeps.lean > $OUT/sd.log 2>&1 && echo "trust: PASS" || { echo "trust: FAIL"; grep -v "^    " $OUT/sd.log | grep -iE "error|fail|rests|witness|pin|unused|frozen|CLAIM|COMPOSITE|FORMULA|label|kind|agreement|inline" | head -20; }
echo "--- numbers"; python3 scripts/trust/check_numbers.py 2>&1 | tail -4
echo "--- prose"; python3 scripts/trust/check_prose.py 2>&1 | tail -25
echo "--- trusted defs"; python3 scripts/trust/check_trusted_defs.py 2>&1 | tail -3
echo "--- formulas"; python3 scripts/trust/check_formulas.py 2>&1 | tail -3
echo "--- provenance"; python3 scripts/trust/check_provenance.py 2>&1 | tail -6
echo "--- claims $(date -u +%T)"; timeout 900 lake env lean scripts/trust/Claims.lean > $OUT/claims.log 2>&1; tail -3 $OUT/claims.log; python3 scripts/trust/check_claims.py 2>&1 | tail -5
echo "--- packet"; python3 validation/make_packet.py 2>&1 | tail -2
cp CLAIMS.md TRUST_MAP.md $OUT/
git add -A >/dev/null; git -c user.email=j@x -c user.name=judge commit -qm "defects $L" >/dev/null 2>&1
echo "--- base diffs vs S (= $BASE + new scripts)"
for s in "check_relock.py $S" "check_numbers.py --base $S" "check_prose.py --base $S" "check_trusted_defs.py --base $S" "check_claims.py --base $S" "check_formulas.py --base $S" "check_provenance.py --base $S"; do
  echo "  [$s]"; python3 scripts/trust/$s 2>&1 | tail -6 | sed 's/^/    /'
done
echo "== AFTER: new scripts $(date -u +%T)"
for s in "check_literals.py" "check_source_names.py" "check_templates.py" "check_literals.py --base $S" "check_source_names.py --base $S" "check_templates.py --base $S" "check_blind_route.py --base $S"; do
  echo "  [$s]"; python3 scripts/trust/$s 2>&1 | tail -12 | sed 's/^/    /'
done
echo "== end $(date -u +%T)"
