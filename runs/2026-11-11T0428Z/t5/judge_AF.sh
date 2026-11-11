#!/bin/bash
# T5 judge for red team AF (run 2026-11-11T0428Z), adapted from runs/2026-11-08T1428Z/t5/judge_W.sh:
# the CI trust and frozen steps of .github/workflows/lean.yml as of the tree, after the author steps
# (relock, Claims, FINDINGS blocks, packet). usage: judge.sh <tree> <base commit> <outdir>
set -u
export PATH=$HOME/.elan/bin:$PATH
TREE=$1; BASE=$2; OUT=$3; mkdir -p $OUT
cd $TREE
echo "== build $(date -u +%T)"
lake build Checked > $OUT/build.log 2>&1 && echo "build: PASS" || { echo "build: FAIL"; grep -m20 "error" $OUT/build.log; }
if grep -rnE '\b(sorry|admit|axiom|native_decide|implemented_by|debug\.skipKernelTC)\b' Checked Checked.lean; then echo "grep: FAIL"; else echo "grep: PASS"; fi
echo "== trust (author relock) $(date -u +%T)"
TRUST_RELOCK=1 timeout 2400 lake env lean scripts/trust/StatementDeps.lean > $OUT/sd.log 2>&1 && echo "trust: PASS" || { echo "trust: FAIL"; grep -v "^    " $OUT/sd.log | grep -iE "error" | head -20; }
echo "--- claims $(date -u +%T)"; timeout 1200 lake env lean scripts/trust/Claims.lean > $OUT/claims.log 2>&1; echo "claims exit $?"; grep -iE "error" $OUT/claims.log | head
python3 scripts/trust/check_numbers.py --write 2>&1 | tail -2
python3 validation/make_packet.py 2>&1 | tail -2
cp CLAIMS.md TRUST_MAP.md $OUT/
git add -A >/dev/null; git -c user.email=j@x -c user.name=judge commit -qm "defects" >/dev/null 2>&1
echo "== CI non-relock trust step $(date -u +%T)"
timeout 2400 lake env lean scripts/trust/StatementDeps.lean > $OUT/sd2.log 2>&1 && echo "trust(CI): PASS" || { echo "trust(CI): FAIL"; grep -iE "error" $OUT/sd2.log | head -20; }
git diff --stat
S=$BASE
for c in check_numbers.py check_prose.py check_literals.py check_source_names.py check_templates.py check_literal_targets.py check_source_variants.py check_prose_gen.py check_prose_eval.py check_claim_words.py check_trusted_defs.py check_claims.py check_claim_vocab.py check_status_lines.py check_necessity.py \
  "check_relock.py $S" "check_numbers.py --base $S" "check_prose.py --base $S" "check_trusted_defs.py --base $S" "check_claims.py --base $S" "check_formulas.py --base $S" "check_provenance.py --base $S" \
  "check_literals.py --base $S" "check_source_names.py --base $S" "check_templates.py --base $S" "check_blind_route.py --base $S" "check_literal_targets.py --base $S" "check_source_variants.py --base $S" "check_prose_gen.py --base $S" "check_reader_frozen.py --base $S" "check_brief_leak.py --base $S" "check_prose_eval.py --base $S" "check_claim_words.py --base $S" "check_claim_vocab.py --base $S" "check_necessity.py --base $S" "check_audits.py $S"; do
  python3 scripts/trust/$c > $OUT/py.tmp 2>&1; rc=$?; echo "  [$c] exit $rc: $(tail -1 $OUT/py.tmp | cut -c1-200)"; [ $rc != 0 ] && tail -15 $OUT/py.tmp | sed 's/^/      /'
done
echo "--- make_packet --check"; python3 validation/make_packet.py --check 2>&1 | tail -2
echo "--- goal guard"; python3 scripts/goal_guard.py 2>&1 | tail -2
echo "--- precheck"; python3 scripts/trust/precheck_citations.py 2>&1 | tail -2
echo "== end $(date -u +%T)"
