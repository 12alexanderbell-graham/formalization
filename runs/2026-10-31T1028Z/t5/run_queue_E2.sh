#!/bin/bash
# reordered (run 1028Z): defects that add new modules first (fast), docstring edits of base modules last
R=/home/claude/formalization/runs/2026-10-31T1028Z/t5
while pgrep -f "judge_v6.sh" > /dev/null; do sleep 15; done
W=/home/claude/fz2 $R/judge_v6.sh $R/ports/Dd04 $R/results/Dd04p.txt
for n in 01 07 08 06 04; do
  W=/home/claude/fz2 $R/judge_v6.sh $R/redteamE/d$n $R/results/Ed$n.txt
done
echo E2_DONE
