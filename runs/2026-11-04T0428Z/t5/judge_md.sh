#!/bin/bash
# Fast judge for defects that edit only *.md records (run 2026-11-04T0428Z): the Lean outputs
# (.lake/meaning.jsonl, records tsv, TRUST_MAP) do not depend on *.md files, so they are taken from
# the full judge run of the clean tree at the same base (control); then every python check of CI
# (v6: numbers, prose, packet, relock/numbers/prose --base; v7 adds check_trusted_defs) runs as in CI.
# Not re-run: StatementDeps' citation check of STATE/FINDINGS (the md defects cite no new constants;
# verified by grep in the results). Usage: judge_md.sh <v6|v7> <defect dir> <out>
set -u
W=${W:-/home/claude/fz2}; V=$1; D=$2; OUT=$3
cd $W; BASE=$(git rev-parse HEAD)
{
echo "defect: $D  base: $BASE  judge: md-$V"
python3 $D/apply.py $W || echo "RESULT APPLY_FAILED"
git status --porcelain
echo "--- new dotted citations (StatementDeps citation check not re-run):"; git diff -U0 -- '*.md' | grep '^+' | grep -oE '`?Checked\.[A-Za-z0-9_.]+' | sort -u
N=1; python3 scripts/trust/check_numbers.py && N=0
P=1; python3 scripts/trust/check_prose.py && P=0
if [ $V = v7 ]; then python3 scripts/trust/check_trusted_defs.py || P=1; fi
K=1; python3 validation/make_packet.py > /tmp/claude-0/md_packet.log 2>&1 && K=0 || tail -n 5 /tmp/claude-0/md_packet.log
git add -A >/dev/null; git -c user.email=j@x -c user.name=judge commit -qm defect >/dev/null 2>&1
R=1; python3 scripts/trust/check_relock.py $BASE && python3 scripts/trust/check_numbers.py --base $BASE && python3 scripts/trust/check_prose.py --base $BASE && R=0
if [ $N = 0 ] && [ $P = 0 ] && [ $K = 0 ] && [ $R = 0 ]; then echo "RESULT ${V^^} ACCEPTED"; else echo "RESULT ${V^^} REJECTED numbers=$N prose=$P packet=$K relock=$R"; fi
} > $OUT 2>&1
git reset -q --hard $BASE; git clean -fdq -- Checked Work scripts runs validation
tail -n 1 $OUT
