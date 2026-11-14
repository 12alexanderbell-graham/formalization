#!/bin/bash
# usage: test.sh dNN
BASE=5536d4bd7b8f7c1d141fe87e8c87b801c873de69
W=/home/claude/t5AO/w_$1
rm -rf $W; cp -a /home/claude/fzAO $W
python3 /home/claude/t5AO/$1/apply.py $W || { echo APPLY FAILED; exit 1; }
python3 /home/claude/t5AO/runchecks.py $W $BASE 2>&1 | tail -40
git -C $W status --short | head
