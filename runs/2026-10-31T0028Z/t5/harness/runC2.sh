#!/bin/bash
R=/home/claude/t5/results; H=/home/claude/t5/harness
while [ ! -f $R/done ]; do sleep 20; done
$H/judge_v3.sh NONE $R/control_v3.txt
for d in /home/claude/t5/redteamC/d0*; do $H/judge_v3.sh $d $R/C$(basename $d)_v3.txt; done
$H/judge.sh /home/claude/t5/redteamA/d01 $R/Ad01_v2.txt
$H/judge.sh /home/claude/t5/redteamA/d02 $R/Ad02_v2.txt
echo DONE3 > $R/done3
