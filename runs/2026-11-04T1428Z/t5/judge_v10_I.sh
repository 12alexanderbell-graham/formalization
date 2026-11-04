#!/bin/bash
# T5 judge v10 (run 2026-11-04T1428Z): judge v9 without `lake build Work` (no H defect touches a file Work imports;
# checked: every defect only adds Checked modules, appends to Checked.lean / headlines.txt, or edits README.md),
# on all defects combined. Usage: judgeH.sh <label>  (runs in /home/claude/fz2 as it stands)
set -u
export PATH=$HOME/.elan/bin:$PATH
cd /home/claude/fz2
SP=/tmp/claude-0/-home-claude-formalization/1b9d4ca5-84e3-5ff2-95cc-0a531352eeaf/scratchpad
L=$1
echo "== judge $L $(date -u +%T)"
TRUST_RELOCK=1 timeout 900 lake env lean scripts/trust/StatementDeps.lean > $SP/sd_$L.log 2>&1 && echo "trust: PASS" || { echo "trust: FAIL"; grep -v "^ " $SP/sd_$L.log | grep -iE "error|rests on|witness|pin |never used|cite|imports|FROZEN|registered|RoundsTo|conjunction" | head -20; }
echo "--- numbers"; python3 scripts/trust/check_numbers.py 2>&1 | tail -5
echo "--- prose"; python3 scripts/trust/check_prose.py 2>&1 | tail -40
echo "--- trusted defs"; python3 scripts/trust/check_trusted_defs.py 2>&1 | tail -3
echo "--- packet"; python3 validation/make_packet.py 2>&1 | tail -3
git add -A >/dev/null; git -c user.email=j@x -c user.name=judge commit -qm "defects $L" >/dev/null 2>&1
echo "--- base diffs vs f73ba92"
python3 scripts/trust/check_relock.py f73ba92 2>&1 | tail -5
python3 scripts/trust/check_numbers.py --base f73ba92 2>&1 | tail -3
python3 scripts/trust/check_prose.py --base f73ba92 2>&1 | tail -8
python3 scripts/trust/check_trusted_defs.py --base f73ba92 2>&1 | tail -3
python3 scripts/trust/check_audits.py f73ba92 2>&1 | tail -3
echo "== end $(date -u +%T)"
