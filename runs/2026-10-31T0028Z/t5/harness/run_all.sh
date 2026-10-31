#!/bin/bash
H=/home/claude/t5/harness; R=/home/claude/t5/results
$H/judge.sh NONE $R/control.txt
for t in A B; do for d in /home/claude/t5/redteam$t/d0*; do $H/judge.sh $d $R/$t$(basename $d).txt; done; done
echo ALLDONE > $R/done
