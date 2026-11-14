#!/bin/bash
# usage: runchecks.sh ROOT BASE
cd "$1"; B=$2
for i in 1 2; do python3 scripts/trust/check_numbers.py --write >/dev/null 2>&1; python3 validation/make_packet.py >/dev/null 2>&1; done
git add -A >/dev/null 2>&1; git -c user.email=a@b -c user.name=a commit -qm defect >/dev/null 2>&1
python3 scripts/trust/check_numbers.py --write >/dev/null 2>&1
python3 validation/make_packet.py >/dev/null 2>&1
fail=0
for c in "check_numbers.py" "check_findings.py" "check_prose.py" "check_source_names.py" "check_templates.py" "check_literal_targets.py" "check_source_variants.py" "check_prose_gen.py" "check_prose_eval.py" "check_claim_words.py" "check_trusted_defs.py" "check_claims.py" "check_claim_vocab.py" "check_status_lines.py" "check_necessity.py" "check_necessity_prose.py" \
  "check_relock.py $B" "check_numbers.py --base $B" "check_findings.py --base $B" "check_prose.py --base $B" "check_trusted_defs.py --base $B" "check_claims.py --base $B" "check_formulas.py --base $B" "check_provenance.py --base $B" "check_source_names.py --base $B" "check_templates.py --base $B" "check_blind_route.py --base $B" "check_literal_targets.py --base $B" "check_source_variants.py --base $B" "check_prose_gen.py --base $B" "check_reader_frozen.py --base $B" "check_brief_leak.py --base $B" "check_prose_eval.py --base $B" "check_claim_words.py --base $B" "check_claim_vocab.py --base $B" "check_necessity.py --base $B"; do
  out=$(python3 scripts/trust/$c 2>&1); rc=$?
  if [ $rc -ne 0 ]; then echo "FAIL: $c"; echo "$out" | head -8; fail=1; fi
done
python3 validation/make_packet.py --check >/dev/null 2>&1 || { echo "FAIL: make_packet --check"; fail=1; }
python3 scripts/trust/route_control.py >/dev/null 2>&1 || echo "FAIL route_control"
echo "DONE fail=$fail"
