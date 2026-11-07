#!/bin/bash
# T5 judge Q (run 2026-11-06T2228Z; from judge_P.sh). BEFORE only: the red team's
# snapshot BASE (= the round-O scripts, as they were when red team P wrote its defects blind), the defects applied
# on top in the commit order they state (d02 stages 1, 2 in their own commits), then the CI checked/trust steps.
# Usage: judge_O.sh <label> <base> <redteam dir> d01 ...
set -u
export PATH=$HOME/.elan/bin:$PATH
L=$1; BASE=$2; RT=$3; shift 3
OUT=/home/claude/judgeQ_$L; mkdir -p $OUT
cd /home/claude/fzQ
git reset -q --hard $BASE; git clean -qfd Checked Work scripts runs
S=$BASE
STAGED=""
for d in "$@"; do grep -q -- "--stage" $RT/$d/apply.py && STAGED="$STAGED $d"; done
for st in 1 2; do
  for d in $STAGED; do python3 $RT/$d/apply.py . --stage $st > /dev/null && echo "applied $d stage $st" || echo "APPLY FAILED $d stage $st"; done
  if [ -n "$STAGED" ]; then git add -A >/dev/null; git -c user.email=j@x -c user.name=judge commit -qm "defects $L stage $st" >/dev/null; fi
done
for d in "$@"; do
  if echo " $STAGED " | grep -q " $d "; then python3 $RT/$d/apply.py . --stage 3 > /dev/null && echo "applied $d stage 3" || echo "APPLY FAILED $d stage 3";
  else python3 $RT/$d/apply.py . > /dev/null && echo "applied $d" || echo "APPLY FAILED $d"; fi
done
echo "== new files compile one by one $(date -u +%T)"
for f in $(git status --short --untracked-files=all | awk '/^\?\?/{print $2}' | grep '\.lean$' | grep -v '^runs/'); do
  timeout 900 lake env lean $f > $OUT/compile_$(basename $f).log 2>&1 && echo "  ok $f" || { echo "  FAIL $f"; grep -m5 error $OUT/compile_$(basename $f).log; }
done
echo "== build $(date -u +%T)"
lake build Checked > $OUT/build.log 2>&1 && echo "build: PASS" || { echo "build: FAIL"; grep -m10 "error" $OUT/build.log; }
for m in $(git status --short --untracked-files=all | awk '{print $2}' | grep '^Work/.*\.lean$' | sed 's/\.lean$//; s#/#.#g'); do
  lake build $m > $OUT/work_$m.log 2>&1 && echo "work $m: PASS" || { echo "work $m: FAIL"; grep -m5 error $OUT/work_$m.log; }
done
if grep -rnE '\b(sorry|admit|axiom|native_decide|implemented_by|debug\.skipKernelTC)\b' Checked Checked.lean; then echo "grep: FAIL"; else echo "grep: PASS"; fi
echo "== trust $(date -u +%T)"
TRUST_RELOCK=1 timeout 1500 lake env lean scripts/trust/StatementDeps.lean > $OUT/sd.log 2>&1 && echo "trust: PASS" || { echo "trust: FAIL"; grep -v "^    " $OUT/sd.log | grep -iE "error|fail|rests|witness|pin|unused|frozen|CLAIM|COMPOSITE|FORMULA|label|kind|agreement|inline" | head -20; }
echo "--- claims $(date -u +%T)"; timeout 900 lake env lean scripts/trust/Claims.lean > $OUT/claims.log 2>&1; tail -3 $OUT/claims.log
python3 validation/make_packet.py 2>&1 | tail -2
cp CLAIMS.md TRUST_MAP.md $OUT/
git add -A >/dev/null; git -c user.email=j@x -c user.name=judge commit -qm "defects $L" >/dev/null 2>&1
echo "== python checks, each separately $(date -u +%T)"
for s in check_numbers.py check_prose.py check_trusted_defs.py check_formulas.py check_provenance.py check_claims.py check_literals.py check_source_names.py check_templates.py check_literal_targets.py check_source_variants.py check_prose_gen.py check_prose_eval.py check_claim_words.py check_claim_vocab.py check_status_lines.py \
  "check_relock.py $S" "check_numbers.py --base $S" "check_prose.py --base $S" "check_trusted_defs.py --base $S" "check_claims.py --base $S" "check_formulas.py --base $S" "check_provenance.py --base $S" \
  "check_literals.py --base $S" "check_source_names.py --base $S" "check_templates.py --base $S" "check_blind_route.py --base $S" "check_literal_targets.py --base $S" "check_source_variants.py --base $S" "check_prose_gen.py --base $S" "check_reader_frozen.py --base $S" "check_brief_leak.py --base $S" "check_prose_eval.py --base $S" "check_claim_words.py --base $S" "check_claim_vocab.py --base $S"; do
  echo "  [$s]"; python3 scripts/trust/$s 2>&1 | tail -8 | sed 's/^/    /'
done
echo "--- make_packet --check"; python3 validation/make_packet.py --check 2>&1 | tail -3
echo "--- goal guard"; python3 scripts/goal_guard.py 2>&1 | tail -3
echo "== end $(date -u +%T)"
