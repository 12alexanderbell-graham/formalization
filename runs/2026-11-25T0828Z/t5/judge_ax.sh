#!/usr/bin/env bash
# Judge of blind round AX (run 2026-11-25T0828Z; copied from runs/2026-11-25T0228Z/t5/judge_aw.sh). For each defect:
# reset the judge tree to BASE (git reset --hard, git clean outside .lake), apply, rerun StatementDeps.lean only when the
# defect touched one of its inputs or any .lean file (else the clean run's .lake outputs serve), regenerate CLAIMS.md /
# CLAIMS_READER.md / PHRASE_LINES.md with Claims.lean and the packet as the author does, save the defect's page, then run
# every Python command of the goal guard, the packet check, and lean.yml's trust and frozen steps with BASE.
# Usage: judge_aw.sh <judge tree> <defects dir> <base sha> <label>   (prints one verdict line per defect)
set -u
J="$1"; D="$2"; BASE="$3"; LABEL="$4"
cd "$J"
source "$HOME/.elan/env"
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
SDIN='scripts/trust/(frozen|pins|def_kinds|headlines|claim_baseline|formula_baseline)\.txt|^FINDINGS\.md|^STATE\.md|\.lean$'
mkdir -p "$D/.judge"; cp -a .lake/meaning.jsonl .lake/necessity.tsv .lake/records_numbers.tsv .lake/records_params.tsv .lake/phrases.jsonl "$D/.judge/" 2>/dev/null
for d in ${ONLY:-clean $(ls "$D" | grep '^d[0-9]')}; do
  git reset -q --hard "$BASE"; git clean -qfd -e .lake
  for f in meaning.jsonl necessity.tsv records_numbers.tsv records_params.tsv phrases.jsonl; do cp -a "$D/.judge/$f" .lake/ 2>/dev/null; done
  out="$D/${d}"; mkdir -p "$out"
  if [ "$d" != clean ]; then python3 "$D/$d/apply.py" "$J" > "$out/apply.log" 2>&1 || { echo "$LABEL $d: APPLY FAILED $(tail -n1 "$out/apply.log")"; continue; }; fi
  changed=$( (git diff --name-only "$BASE"; git ls-files --others --exclude-standard) | sort -u)
  lean_fail=""
  if [ "$d" = clean ]; then sd="clean outputs of BASE"; # the clean tree's .lake outputs and generated pages are BASE's own (StatementDeps and Claims.lean run on BASE before the round)
  elif echo "$changed" | grep -Eq "$SDIN"; then
    lake env lean scripts/trust/StatementDeps.lean > "$out/statementdeps.log" 2>&1 || lean_fail="$lean_fail | StatementDeps :: $(grep -m1 -i 'error' "$out/statementdeps.log" | cut -c1-220)"
    sd="rerun"
  else sd="reused"; fi
  # SKIP_CLAIMS=1 (used for round AV, whose five apply.py write the pages themselves): no per-defect Claims.lean; the
  # generated pages are verified once instead, by Claims.lean on the tree with every defect applied (git diff empty).
  [ "$d" = clean ] || [ "${SKIP_CLAIMS:-0}" = 1 ] || lake env lean scripts/trust/Claims.lean > "$out/claims.log" 2>&1 || lean_fail="$lean_fail | Claims.lean :: $(grep -m1 -i 'error' "$out/claims.log" | cut -c1-220)"
  python3 validation/make_packet.py > /dev/null 2>&1
  cp CLAIMS_READER.md "$out/CLAIMS_READER.page"
  fails="$lean_fail"
  while IFS= read -r c; do
    o=$(BASE="$BASE" bash -c "${c//\$BASE/$BASE}" 2>&1)
    rc=$?
    # Round AW: BASE is the brief commit, not a green ancestor, so check_stale_status (inside check_headline_mentions)
    # flags the pending heading of third_coefficient_lower_bound on the clean tree too (STATE.md:117; CI's base is the
    # newest green ancestor, where it does not fire). Only findings beyond that clean one count.
    if [ $rc -ne 0 ] && [[ "$c" == *check_headline_mentions* ]]; then
      extra=$(echo "$o" | grep -E '^[^ ]+:[0-9]+: ' | grep -v 'STALE pending status' | head -1)
      [ -z "$extra" ] && rc=0
    fi
    [ $rc -eq 0 ] || fails="$fails | ${c#python3 scripts/trust/} :: $(echo "$o" | grep -m1 -i 'error\|fail\|::' | cut -c1-220)"
  done <<< "$CHECKS"
  if [ -z "$fails" ]; then echo "$LABEL $d (StatementDeps $sd): ACCEPTED (every check green)"; else echo "$LABEL $d (StatementDeps $sd): CAUGHT$fails"; fi
done
git reset -q --hard "$BASE"; git clean -qfd -e .lake
