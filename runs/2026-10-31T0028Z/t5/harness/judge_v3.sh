#!/bin/bash
# T5 judge v2 (run 0028Z): apply one seeded defect, run the CI-replica checks as of run 2228Z ("before")
# and the strengthened checks of run 0028Z ("after", from /home/claude/t5/new) on the same build, restore.
set -u
REPO=/home/claude/formalization; D=$1; OUT=$2; NEW=/home/claude/t5/new3
export PATH=$HOME/.elan/bin:$PATH
cd $REPO
if [ -n "$(git status --porcelain -- Checked Work scripts Checked.lean Work.lean '*.md')" ]; then echo "DIRTY TREE"; exit 2; fi
{
echo "defect: $D"; date -u +%T
if [ "$D" != NONE ]; then python3 $D/apply.py $REPO || { echo "RESULT APPLY_FAILED"; }; fi
echo "--- changed files"; git status --porcelain
cp TRUST_MAP.md /tmp/map_committed.md
TOUCHED_MAP=0; git diff --quiet -- TRUST_MAP.md || TOUCHED_MAP=1
echo "--- build"
if timeout 1500 lake build Checked > /tmp/judge_build.log 2>&1; then echo "build: PASS"; B=0; else echo "build: FAIL"; B=1; grep -E "error" /tmp/judge_build.log | head -n 15; fi
echo "--- forbidden tokens"
if grep -rnE '\b(sorry|admit|axiom|native_decide|implemented_by|debug\.skipKernelTC)\b' Checked Checked.lean; then echo "tokens: FAIL"; T=1; else echo "tokens: PASS"; T=0; fi
S=1; S2=1; R2=1; M2=0
if [ $B = 0 ]; then
  mkdir -p /tmp/newsd; cp $NEW/StatementDeps.lean /tmp/newsd/SD_new.lean
  ( timeout 900 lake env lean scripts/trust/StatementDeps.lean > /tmp/judge_sd.log 2>&1; echo $? > /tmp/judge_sd.rc ) &
  ( TRUST_RELOCK=1 timeout 900 lake env lean /tmp/newsd/SD_new.lean > /tmp/judge_sd2.log 2>&1; echo $? > /tmp/judge_sd2.rc ) &
  wait
  echo "--- trust step (before: checks as of run 2228Z)"
  if [ "$(cat /tmp/judge_sd.rc)" = 0 ]; then echo "trust: PASS"; S=0; else echo "trust: FAIL"; grep -iE "error|rests on|witness|pin |FROZEN|cites" /tmp/judge_sd.log | grep -v "^\s" | head -n 12; fi
  echo "--- trust step (after: run 0028Z checks; author relocks)"
  if [ "$(cat /tmp/judge_sd2.rc)" = 0 ]; then echo "trust2: PASS"; S2=0; else echo "trust2: FAIL"; grep -iE "error|rests on|witness|pin |never used|cite|not a pin|imports|FROZEN|registered" /tmp/judge_sd2.log | grep -v "^ " | head -n 20; cp /tmp/judge_sd2.log $OUT.sd2.log; fi
  echo "--- relock check (after): changed/removed frozen entries need a LEDGER line naming them"
  python3 - <<'PY' && R2=0
import subprocess,sys
def parse(t):
    d={}
    for l in t.splitlines():
        p=l.split()
        if len(p)==2 and not l.startswith('#'): d[p[0]]=p[1]
    return d
old=parse(open('/home/claude/t5/new3/frozen.txt').read())
try: new=parse(open('scripts/trust/frozen.txt').read())
except FileNotFoundError: print('no regenerated frozen.txt'); sys.exit(1)
ch=[n for n,f in old.items() if new.get(n)!=f]
led=subprocess.run(['git','diff','--','LEDGER.md'],capture_output=True,text=True).stdout
added='\n'.join(l[1:] for l in led.splitlines() if l.startswith('+') and not l.startswith('+++'))
miss=[n for n in ch if n.split('.')[-1] not in added]
print('changed/removed frozen entries:', ch); print('not named in LEDGER:', miss)
sys.exit(1 if miss else 0)
PY
  [ $R2 = 0 ] && echo "relock: PASS" || echo "relock: FAIL"
  if [ $TOUCHED_MAP = 1 ] && ! cmp -s TRUST_MAP.md /tmp/map_committed.md; then M2=1; echo "trust-map: defect hand-edited TRUST_MAP.md and it is stale (blocking after)"; fi
fi
if [ $B = 0 ] && [ $T = 0 ] && [ $S = 0 ]; then echo "RESULT BEFORE ACCEPTED"; else echo "RESULT BEFORE REJECTED build=$B tokens=$T trust=$S"; fi
if [ $B = 0 ] && [ $T = 0 ] && [ $S2 = 0 ] && [ $R2 = 0 ] && [ $M2 = 0 ]; then echo "RESULT AFTER ACCEPTED"; else echo "RESULT AFTER REJECTED build=$B tokens=$T trust2=$S2 relock=$R2 map=$M2"; fi
date -u +%T
} > $OUT 2>&1
git checkout -q -- . ; git clean -fdq -- Checked Work scripts
tail -n 3 $OUT
