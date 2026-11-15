#!/bin/bash
# test1.sh dNN : fresh copy, apply, then checks
N=$1; W=/home/claude/t5AU/work/t_$N; rm -rf $W; cp -a /home/claude/t5AU/work/fzAU $W; cd $W; git checkout -q -- .; git clean -fdq
B=$(git rev-parse HEAD)
python3 /home/claude/t5AU/$N/apply.py $W || { echo APPLYFAIL; exit 1; }
/home/claude/t5AU/runchecks.sh $W $B > /home/claude/t5AU/work/$N.log 2>&1
tail -15 /home/claude/t5AU/work/$N.log
