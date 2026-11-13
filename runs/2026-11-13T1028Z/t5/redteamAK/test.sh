#!/bin/bash
# usage: test.sh dNN
d=$1; rm -rf /home/claude/t5AK/tmp_$d; cp -a /home/claude/t5AK/work /home/claude/t5AK/tmp_$d; cd /home/claude/t5AK/tmp_$d
git checkout -q -- FINDINGS.md LEDGER.md 2>&1; git status --short | head -3
python3 /home/claude/t5AK/$d/apply.py . || exit 1
python3 scripts/trust/check_numbers.py --write >/dev/null 2>&1; python3 validation/make_packet.py >/dev/null 2>&1
git status --short | head
python3 scripts/trust/records_check.py 4af3d97 2>&1 | grep -v "check_literals" | tail -12
