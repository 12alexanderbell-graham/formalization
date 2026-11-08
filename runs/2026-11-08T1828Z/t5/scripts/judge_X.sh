#!/bin/bash
# Judge of blind red team X (run 2026-11-08T1828Z): phrase-only defects, so no Lean module changes; one Claims.lean
# pass per column with that column's generator and phrase checks, on a tree whose .lake is the built main tree's.
# usage: judge_X.sh <tree with defects committed> <base commit> <outdir> <label=sha> [...]
set -u
export PATH=$HOME/.elan/bin:$PATH
TREE=$1; BASE=$2; OUT=$3; shift 3; mkdir -p $OUT
cd $TREE
for col in "$@"; do
  L=${col%%=*}; C=${col#*=}
  echo "== column $L (generator and checks of $C) $(date -u +%T)"
  for f in scripts/trust/Claims.lean scripts/trust/check_claims.py scripts/trust/check_numbers.py scripts/trust/check_claim_vocab.py; do
    git -C /home/claude/formalization show $C:$f > $f; done
  timeout 900 lake env lean scripts/trust/Claims.lean > $OUT/claims_$L.log 2>&1; echo "  Claims.lean exit $?"; grep -iE "error" $OUT/claims_$L.log | head -5
  cp CLAIMS.md $OUT/CLAIMS_$L.md
  python3 scripts/trust/check_numbers.py --write > /dev/null 2>&1
  for s in check_claims.py "check_claims.py --base $BASE" check_claim_vocab.py check_numbers.py; do
    echo "  [$s]"; python3 scripts/trust/$s > $OUT/$(echo $L-$s | tr ' /' '__').log 2>&1; echo "    exit $?"; tail -12 $OUT/$(echo $L-$s | tr ' /' '__').log | sed 's/^/    /'
  done
  git checkout -q -- . ; git clean -qfd scripts
done
echo "== end $(date -u +%T)"
