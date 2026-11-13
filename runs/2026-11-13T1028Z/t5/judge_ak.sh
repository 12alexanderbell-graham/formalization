#!/usr/bin/env bash
# Judge of blind round AK (run 2026-11-13T1028Z; copy of runs/2026-11-13T0028Z/t5/judge_aj.sh; also resets LEDGER.md and scripts/trust/*.txt between defects). Every defect edits FINDINGS.md only (no Lean), so the Lean outputs
# (.lake/records_numbers.tsv, meaning.jsonl, ...) of one StatementDeps run on the clean tree serve every defect.
# Usage: judge_ai.sh <judge tree> <defects dir> <base sha> <label>   (prints one verdict line per defect)
set -u
J="$1"; D="$2"; BASE="$3"; LABEL="$4"
cd "$J"
CHECKS=$(python3 - <<'PY'
import sys
sys.path.insert(0, 'scripts/trust')
from local_frozen_step import step_block, step_commands, TRUST_STEP
y = open('.github/workflows/lean.yml').read()
b = [l.strip() for l in step_block(y, TRUST_STEP).splitlines() if l.strip().startswith('python3')]
f = [c for c in step_commands(y) if c.startswith('python3')]
print('\n'.join(['python3 scripts/goal_guard.py', 'python3 validation/make_packet.py --check'] + b + f))
PY
)
for d in clean $(ls "$D" | grep '^d[0-9]'); do
  git checkout -q -- FINDINGS.md LEDGER.md scripts/trust validation 2>/dev/null
  if [ "$d" != clean ]; then python3 "$D/$d/apply.py" "$J" > /tmp/claude-0/apply.log 2>&1 || { echo "$LABEL $d: APPLY FAILED $(tail -n1 /tmp/claude-0/apply.log)"; continue; }; fi
  # the author regenerates the certified blocks and the validation packet
  python3 scripts/trust/check_numbers.py --write > /dev/null 2>&1
  python3 validation/make_packet.py > /dev/null 2>&1
  fails=""
  while IFS= read -r c; do
    out=$(BASE="$BASE" bash -c "${c//\$BASE/$BASE}" 2>&1) || fails="$fails | ${c#python3 scripts/trust/} :: $(echo "$out" | grep -m1 -i 'error\|fail\|::' | cut -c1-220)"
  done <<< "$CHECKS"
  if [ -z "$fails" ]; then echo "$LABEL $d: ACCEPTED (every check green)"; else echo "$LABEL $d: CAUGHT$fails"; fi
done
git checkout -q -- FINDINGS.md LEDGER.md scripts/trust validation 2>/dev/null
