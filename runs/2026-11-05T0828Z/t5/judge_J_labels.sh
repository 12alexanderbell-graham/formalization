#!/bin/bash
# Re-judge red team J's accepted name/constant defects d03, d06 (run 2026-11-04T2228Z) against the
# label rules of run 2026-11-05T0828Z, under every label an attacker could choose for the new
# definitions. Runs in the main tree (restored after each defect); needs a built Checked.
set -u
cd "$(git rev-parse --show-toplevel)"
source ~/.elan/env
J=runs/2026-11-04T2228Z/t5/redteamJ
OUT=runs/2026-11-05T0828Z/t5/judge_J_labels.txt
: > $OUT
for d in d03 d06; do
  python3 $J/$d/apply.py . > /dev/null
  lake build Checked > /tmp/jl_build_$d.log 2>&1 || { echo "$d build FAILED" >> $OUT; }
  cp scripts/trust/def_kinds.txt /tmp/kinds_$d.txt
  for label in FORMULA COMPOSITE MATH WITNESS SPEC CLAIM PRINTED FOO; do
    sed -E "s/^(Checked\.Chemistry\.(VdWScale|BoyleScale)\.[A-Za-z]+) FORMULA$/\1 $label/" /tmp/kinds_$d.txt > scripts/trust/def_kinds.txt
    TRUST_RELOCK=1 lake env lean scripts/trust/StatementDeps.lean > /tmp/jl_${d}_${label}.log 2>&1
    rc=$?
    errs=$(grep -E "error" /tmp/jl_${d}_${label}.log | grep -E "VdWScale|BoyleScale|tempScale|boyleT|tcScale" | head -3 | tr '\n' ' ' | cut -c1-400)
    if [ $rc -eq 0 ] && [ -z "$errs" ]; then verdict=ACCEPTED; else verdict=REJECTED; fi
    echo "$d $label $verdict rc=$rc :: $errs" >> $OUT
  done
  git checkout -q -- Checked.lean scripts/trust/headlines.txt scripts/trust/def_kinds.txt TRUST_MAP.md scripts/trust/frozen.txt 2>/dev/null
  git clean -fdq Checked/Chemistry/
  rm -f Checked/Chemistry/VdWScale.lean Checked/Chemistry/BoyleScale.lean
done
cat $OUT
