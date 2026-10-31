#!/bin/bash
R=/home/claude/t5/results
while [ ! -f $R/done ]; do sleep 20; done
H=/home/claude/t5/harness
$H/judge.sh NONE $R/control_v2.txt
$H/judge.sh /home/claude/t5/redteamA/d01 $R/Ad01_v2.txt
$H/judge.sh /home/claude/t5/redteamA/d02 $R/Ad02_v2.txt
echo DONE2 > $R/done2
