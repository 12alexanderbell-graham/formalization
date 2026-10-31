#!/bin/bash
# Judge every 0028Z defect (ports where the tagged records changed the target text) with judge v5.
H=/home/claude/formalization/runs/2026-10-31T0228Z/t5; O=/home/claude/formalization/runs/2026-10-31T0028Z/t5
R=/tmp/t5v5; mkdir -p $R
$H/judge_v5.sh NONE $R/control.txt
for t in A B C; do for d in $O/redteam$t/d0*; do n=$t$(basename $d)
  if [ -d $H/ports/$n ]; then d=$H/ports/$n; fi
  $H/judge_v5.sh $d $R/$n.txt; done; done
$H/judge_v5.sh $H/ports/Bd07s $R/Bd07s.txt
echo ALLDONE > $R/done
