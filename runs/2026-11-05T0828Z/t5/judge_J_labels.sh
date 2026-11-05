#!/bin/bash
# Re-judge red team J's accepted name/constant defects d03 (tempScale) and d06 (boyleT, tcScale)
# (run 2026-11-04T2228Z) against the label rules of run 2026-11-05T0828Z, with the new definitions
# under the labels an attacker could choose. Both defects applied together; each label assignment
# is one trust-step run (author relock, as in the J judge). Main tree, restored afterwards.
set -u
cd "$(git rev-parse --show-toplevel)"
source ~/.elan/env
J=runs/2026-11-04T2228Z/t5/redteamJ
OUT=runs/2026-11-05T0828Z/t5/judge_J_labels.txt
: > $OUT
python3 $J/d03/apply.py . > /dev/null && python3 $J/d06/apply.py . > /dev/null
lake build Checked > /tmp/jl_build.log 2>&1 || echo "build FAILED" >> $OUT
cp scripts/trust/def_kinds.txt /tmp/kinds_j.txt
run() {  # $1 tempScale label, $2 boyleT label, $3 tcScale label
  sed -E "s/^(Checked\.Chemistry\.VdWScale\.tempScale) FORMULA$/\1 $1/; s/^(Checked\.Chemistry\.BoyleScale\.boyleT) FORMULA$/\1 $2/; s/^(Checked\.Chemistry\.BoyleScale\.tcScale) FORMULA$/\1 $3/" /tmp/kinds_j.txt > scripts/trust/def_kinds.txt
  TRUST_RELOCK=1 lake env lean scripts/trust/StatementDeps.lean > /tmp/jl_$1.log 2>&1
  echo "rc=$? labels tempScale=$1 boyleT=$2 tcScale=$3" >> $OUT
  grep -E "tempScale|boyleT|tcScale|VdWScale|BoyleScale" /tmp/jl_$1.log | grep -vE "^    |^Checked\.Chemistry" | sed 's/^/  /' >> $OUT
}
run FORMULA COMPOSITE SPEC
run MATH PRINTED FOO
run WITNESS CLAIM COMPOSITE
git checkout -q -- Checked.lean scripts/trust/headlines.txt scripts/trust/def_kinds.txt TRUST_MAP.md scripts/trust/frozen.txt
rm -f Checked/Chemistry/VdWScale.lean Checked/Chemistry/BoyleScale.lean
git status --short
cat $OUT
