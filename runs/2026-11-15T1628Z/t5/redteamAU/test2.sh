#!/bin/bash
N=$1; W=/home/claude/t5AU/work/fzAU; cd $W; git reset -q --hard 25a8b953; git clean -fdq
B=$(git rev-parse HEAD)
python3 /home/claude/t5AU/$N/apply.py $W > /home/claude/t5AU/work/$N.apply 2>&1 || { echo APPLYFAIL >> /home/claude/t5AU/work/$N.apply; exit 1; }
/home/claude/t5AU/runchecks.sh $W $B > /home/claude/t5AU/work/$N.log 2>&1
echo FINISHED >> /home/claude/t5AU/work/$N.log
