#!/bin/bash
# T5 judge P, AFTER (run 2026-11-06T2228Z; NOT blind: the new rules were written after reading P's report).
# Runs in the judged tree left by judge_P.sh (defects applied, meaning.jsonl and CLAIMS.md of that tree): copies the
# rules of this run from main (check_claim_words W2 with namespaces, check_claim_vocab V1-V5, check_status_lines S1,
# the Claims.lean notation block), regenerates CLAIMS.md, and reports the findings on the defects' headlines and
# STATE.md. The vocabulary baseline of main lists main's headlines (Thomas–Fermi ones are absent at the red team's
# base), so findings are read per defect with --report rather than as the pass/fail of the baseline comparison.
set -u
export PATH=$HOME/.elan/bin:$PATH
M=/home/claude/formalization; OUT=/home/claude/judgeP_${1:-all}
cd /home/claude/fzP
for f in check_claim_words.py check_claim_vocab.py check_status_lines.py claim_vocab_baseline.txt prose_vocab.txt Claims.lean; do cp $M/scripts/trust/$f scripts/trust/$f; done
timeout 900 lake env lean scripts/trust/Claims.lean > $OUT/claims_after.log 2>&1; tail -2 $OUT/claims_after.log
echo "== check_claim_words (W1-W5, --report)"; python3 scripts/trust/check_claim_words.py --report | grep -E "GelfandPeak|rob_y2_bound|RobertsonAllTimes|critical_bracket|inverted_frequency" | sed 's/^/  /'
echo "== check_claim_vocab (V1, V5, --report)"; python3 scripts/trust/check_claim_vocab.py --report | grep -E "GelfandPeak|rob_y2_bound|RobertsonAllTimes|critical_bracket|inverted_frequency" | sed 's/^/  /'
echo "== check_status_lines"; python3 scripts/trust/check_status_lines.py | sed 's/^/  /'
echo "== end $(date -u +%T)"
