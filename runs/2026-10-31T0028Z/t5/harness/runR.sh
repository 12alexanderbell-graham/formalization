#!/bin/bash
R=/home/claude/t5/results; H=/home/claude/t5/harness
while [ ! -f $R/done3 ]; do sleep 20; done
$H/judge_v3.sh /home/claude/t5/redteamA/d08r $R/Ad08r_v3.txt
echo DONE4 > $R/done4
