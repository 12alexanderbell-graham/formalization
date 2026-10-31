#!/bin/bash
# Final queue (run 0228Z) at the last check version: control, defects judged before a later fix, and
# defects first scored on the stale-map rule.
H=/home/claude/formalization/runs/2026-10-31T0228Z/t5; O=/home/claude/formalization/runs/2026-10-31T0028Z/t5; R=$H/results
# (started after the priority queue was stopped)
cd /home/claude/fz2 && git checkout -q --detach $1
$H/judge_v5.sh NONE $R/final_control.txt
$H/judge_v5.sh $H/ports/Dd02 $R/final_Dd02.txt
$H/judge_v5.sh $O/redteamC/d06 $R/final_Cd06.txt
$H/judge_v5.sh $O/redteamA/d05 $R/final_Ad05.txt
$H/judge_v5.sh $O/redteamB/d04 $R/final_Bd04.txt
$H/judge_v5.sh $O/redteamA/d04 $R/final_Ad04.txt
echo ALLDONE > $R/final_done
