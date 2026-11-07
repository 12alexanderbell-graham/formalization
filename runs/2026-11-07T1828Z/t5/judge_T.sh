#!/bin/bash
# T5 judge of red team T (run 2026-11-07T1828Z); copy of runs/2026-11-07T1428Z/t5/judge_RS.sh that also copies the column's controls/ and claim_vocab_baseline.txt and runs check_audits.py (R1).
# usage: judge_RS.sh <tree> <base commit of the tree> <outdir> <label=sha> [<label=sha> ...]
# The tree has the defects applied (uncommitted). Lean side once (build, grep, StatementDeps with relock, Claims,
# packet); then every Python check once per column, with scripts/trust/*.py taken from the column's commit.
set -u
export PATH=$HOME/.elan/bin:$PATH
TREE=$1; BASE=$2; OUT=$3; shift 3; mkdir -p $OUT
cd $TREE
echo "== new files compile one by one $(date -u +%T)"
for f in $(git status --short --untracked-files=all | awk '/^\?\?/{print $2}' | grep '\.lean$' | grep -v '^runs/'); do
  timeout 900 lake env lean $f > $OUT/compile_$(basename $f).log 2>&1 && echo "  ok $f" || { echo "  FAIL $f"; grep -m5 error $OUT/compile_$(basename $f).log; }
done
echo "== build $(date -u +%T)"
lake build Checked > $OUT/build.log 2>&1 && echo "build: PASS" || { echo "build: FAIL"; grep -m10 "error" $OUT/build.log; }
if grep -rnE '\b(sorry|admit|axiom|native_decide|implemented_by|debug\.skipKernelTC)\b' Checked Checked.lean; then echo "grep: FAIL"; else echo "grep: PASS"; fi
echo "== trust $(date -u +%T)"
TRUST_RELOCK=1 timeout 1500 lake env lean scripts/trust/StatementDeps.lean > $OUT/sd.log 2>&1 && echo "trust: PASS" || { echo "trust: FAIL"; grep -v "^    " $OUT/sd.log | grep -iE "error|fail|rests|witness|pin|unused|frozen|CLAIM|COMPOSITE|FORMULA|label|kind|agreement|inline" | head -20; }
echo "--- claims $(date -u +%T)"; timeout 900 lake env lean scripts/trust/Claims.lean > $OUT/claims.log 2>&1; tail -3 $OUT/claims.log
python3 validation/make_packet.py 2>&1 | tail -2
cp CLAIMS.md TRUST_MAP.md $OUT/
git add -A >/dev/null; git -c user.email=j@x -c user.name=judge commit -qm "defects" >/dev/null 2>&1
S=$BASE
run_checks () {
for s in check_numbers.py check_prose.py check_trusted_defs.py check_formulas.py check_provenance.py check_claims.py check_literals.py check_source_names.py check_templates.py check_literal_targets.py check_source_variants.py check_prose_gen.py check_prose_eval.py check_claim_words.py check_claim_vocab.py check_status_lines.py \
  "check_audits.py $S"   "check_relock.py $S" "check_numbers.py --base $S" "check_prose.py --base $S" "check_trusted_defs.py --base $S" "check_claims.py --base $S" "check_formulas.py --base $S" "check_provenance.py --base $S" \
  "check_literals.py --base $S" "check_source_names.py --base $S" "check_templates.py --base $S" "check_blind_route.py --base $S" "check_literal_targets.py --base $S" "check_source_variants.py --base $S" "check_prose_gen.py --base $S" "check_reader_frozen.py --base $S" "check_brief_leak.py --base $S" "check_prose_eval.py --base $S" "check_claim_words.py --base $S" "check_claim_vocab.py --base $S"; do
  echo "  [$s]"; python3 scripts/trust/$s 2>&1 | tail -8 | sed 's/^/    /'
done
echo "--- make_packet --check"; python3 validation/make_packet.py --check 2>&1 | tail -3
echo "--- goal guard"; python3 scripts/goal_guard.py 2>&1 | tail -3
python3 scripts/trust/precheck_citations.py 2>&1 | tail -3
}
for col in "$@"; do
  L=${col%%=*}; C=${col#*=}
  echo "== column $L (scripts/trust/*.py of $C) $(date -u +%T)"
  for f in $(git -C /home/claude/formalization ls-tree --name-only $C scripts/trust/ | grep '\.py$'); do git -C /home/claude/formalization show $C:$f > $f; done
  for f in scripts/trust/controls/prose_rule_controls.py scripts/trust/claim_vocab_baseline.txt; do git -C /home/claude/formalization show $C:$f > $f; done
  run_checks
  git checkout -q scripts/trust
done
echo "== end $(date -u +%T)"
