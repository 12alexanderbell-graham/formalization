#!/bin/bash
R=/home/claude/formalization/runs/2026-10-31T1028Z/t5
while ! grep -q E_DONE /tmp/queueE.log; do sleep 20; done
W=/home/claude/fz2 $R/judge_v6.sh $R/ports/Dd04 $R/results/Dd04p.txt
echo PORT_DONE
