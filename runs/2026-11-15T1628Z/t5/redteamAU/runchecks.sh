#!/bin/bash
# usage: runchecks.sh ROOT BASE  -- regenerate then run non-Lean checks
R=$1; B=$2; cd $R
python3 scripts/trust/check_numbers.py --write >/dev/null 2>&1
python3 validation/make_packet.py >/dev/null 2>&1
python3 scripts/trust/make_verified_page.py 2>&1 | tail -2
fail=0
run(){ out=$("$@" 2>&1); rc=$?; if [ $rc -ne 0 ]; then echo "FAIL($rc): $*"; echo "$out" | tail -6 | cut -c1-400; fail=1; fi; }
run python3 scripts/trust/route_control.py
run python3 scripts/trust/check_findings.py --render
run python3 scripts/trust/make_verified_page.py --selftest
run python3 scripts/trust/make_verified_page.py --check
run python3 scripts/trust/check_numbers.py
run python3 scripts/trust/check_findings.py
run python3 scripts/trust/check_numbers.py --base $B
run python3 scripts/trust/check_findings.py --base $B
for s in check_relock check_trusted_defs check_claims check_formulas check_provenance check_literals check_source_names check_templates check_blind_route check_literal_targets check_source_variants check_prose_gen check_reader_frozen check_brief_leak check_prose_eval check_claim_words check_claim_vocab check_necessity check_prose; do
 run python3 scripts/trust/$s.py --base $B; done
run python3 validation/make_packet.py --check
echo "done fail=$fail"
