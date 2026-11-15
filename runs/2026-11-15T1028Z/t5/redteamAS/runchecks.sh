#!/bin/bash
# usage: runchecks.sh ROOT  (runs non-Lean checks; prints failures)
R=$1; BASE=c78c59d59a5c33b0c6b6b4a215add08099fb7894
cd $R
fail=0
run(){ out=$("$@" 2>&1); rc=$?; if [ $rc -ne 0 ]; then echo "FAIL($rc): $*"; echo "$out" | tail -8 | cut -c1-400; fail=1; fi; }
run python3 scripts/trust/check_numbers.py
run python3 scripts/trust/check_findings.py
run python3 scripts/trust/check_findings.py --render
run python3 scripts/trust/check_findings.py --base $BASE
run python3 scripts/trust/check_numbers.py --base $BASE
run python3 validation/make_packet.py --check
for c in check_prose check_literals check_source_names check_templates check_literal_targets check_source_variants check_prose_gen check_prose_eval check_claim_words check_trusted_defs check_claims check_claim_vocab check_status_lines check_necessity check_necessity_prose; do run python3 scripts/trust/$c.py; done
for c in check_relock check_prose check_trusted_defs check_claims check_formulas check_provenance check_literals check_source_names check_templates check_blind_route check_literal_targets check_source_variants check_prose_gen check_reader_frozen check_brief_leak check_prose_eval check_claim_words check_claim_vocab check_necessity; do run python3 scripts/trust/$c.py --base $BASE; done
run python3 scripts/trust/check_relock.py $BASE
run python3 scripts/goal_guard.py
[ $fail = 0 ] && echo ALLGREEN
