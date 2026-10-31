#!/bin/bash
# queue for judge v6 (run 1028Z): control, then the open T5 holes from runs 0028Z/0228Z
R=/home/claude/formalization/runs/2026-10-31T1028Z/t5
A=/home/claude/formalization/runs/2026-10-31T0028Z/t5
D=/home/claude/formalization/runs/2026-10-31T0228Z/t5
for pair in "control NONE" "Ad04 $A/redteamA/d04" "Bd04 $A/redteamB/d04" "Ad05 $A/redteamA/d05" "Dd04 $D/redteamD/d04" "Ad03 $A/redteamA/d03" "Dd01 $D/redteamD/d01"; do
  set -- $pair
  W=/home/claude/fz2 $R/judge_v6.sh $2 $R/results/$1.txt
done
echo QUEUE_DONE
