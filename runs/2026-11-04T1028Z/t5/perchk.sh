#!/bin/bash
# run every python check and AuditClosed individually on fz2 with the G defects applied (after judge v9)
cd /home/claude/fz2; export PATH=$HOME/.elan/bin:$PATH; B=7d4553b
for d in /home/claude/t5G/d0*; do python3 $d/apply.py . > /dev/null 2>&1 || echo "$d FAIL"; done
TRUST_RELOCK=1 timeout 900 lake env lean scripts/trust/StatementDeps.lean > /tmp/claude-0/pc_sd.log 2>&1; echo "trust rc=$?"
git add -A >/dev/null; git -c user.email=j@x -c user.name=judge commit -qm defect
echo "== prose"; python3 scripts/trust/check_prose.py | cut -c1-220
echo "== numbers"; python3 scripts/trust/check_numbers.py | tail -3 | cut -c1-200
echo "== trusted"; python3 scripts/trust/check_trusted_defs.py --base $B | cut -c1-220
echo "== relock"; python3 scripts/trust/check_relock.py $B | cut -c1-300 | head -20
echo "== audits"; python3 scripts/trust/check_audits.py $B; timeout 600 lake env lean scripts/trust/AuditClosed.lean 2>&1 | tail -3
git reset -q --hard $B; git clean -fdq -- Checked Work scripts runs
