#!/bin/bash
# T5 judge for blind red team K (run 2026-11-05T1428Z): all valid defects combined in the worktree
# /home/claude/fz3 (base 01b0c8c, defects applied and built); runs every CI trust-step check and every
# --base diff exactly as .github/workflows/lean.yml, with the author's relock and regenerated
# TRUST_MAP.md / CLAIMS.md / packet. Usage: judge_K.sh <label> [<dir with scripts/trust to copy in>]
set -u
export PATH=$HOME/.elan/bin:$PATH
cd /home/claude/fz3
L=$1; OUT=/home/claude/t5K/judge_$L; mkdir -p $OUT
BASE=01b0c8c
if [ $# -ge 2 ]; then cp $2/scripts/trust/*.py $2/scripts/trust/*.lean scripts/trust/; cp $2/scripts/trust/claim_baseline.txt $2/scripts/trust/prose_baseline.txt scripts/trust/; fi
echo "== judge $L $(date -u +%T)"
TRUST_RELOCK=1 timeout 1200 lake env lean scripts/trust/StatementDeps.lean > $OUT/sd.log 2>&1 && echo "trust (relock): PASS" || echo "trust (relock): FAIL"
lake env lean scripts/trust/Claims.lean > $OUT/claims.log 2>&1 && echo "Claims.lean: PASS" || echo "Claims.lean: FAIL"
python3 validation/make_packet.py > $OUT/packet.log 2>&1
git add -A >/dev/null; git -c user.email=j@x -c user.name=judge commit -qm "defects $L (author relock + regeneration)" >/dev/null 2>&1
lake env lean scripts/trust/Claims.lean > $OUT/claims2.log 2>&1
git diff --quiet -- CLAIMS.md TRUST_MAP.md && echo "CLAIMS/TRUST_MAP fresh: PASS" || echo "CLAIMS/TRUST_MAP fresh: FAIL"
for c in "check_numbers.py" "check_prose.py" "check_trusted_defs.py" "check_claims.py"; do
  python3 scripts/trust/$c > $OUT/$c.log 2>&1 && echo "$c: PASS" || echo "$c: FAIL"; done
python3 validation/make_packet.py --check > $OUT/packet_check.log 2>&1 && echo "packet --check: PASS" || echo "packet --check: FAIL"
for c in check_relock.py check_numbers.py check_prose.py check_trusted_defs.py check_claims.py check_formulas.py; do
  a=$BASE; [ $c = check_relock.py ] || a="--base $BASE"
  python3 scripts/trust/$c $a > $OUT/base_$c.log 2>&1 && echo "$c --base: PASS" || echo "$c --base: FAIL"; done
python3 scripts/goal_guard.py > $OUT/goal.log 2>&1 && echo "goal guard: PASS" || echo "goal guard: FAIL"
echo "== end $(date -u +%T)"
