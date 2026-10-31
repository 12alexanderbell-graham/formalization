#!/bin/bash
# red team E, judged by judge v6 at the checks of commit 38e8efb (after the E-driven hardening)
R=/home/claude/formalization/runs/2026-10-31T1028Z/t5
while ! grep -q QUEUE_DONE /tmp/queue.log; do sleep 20; done
cd /home/claude/fz2 && git checkout -q --detach 38e8efb36f1337717a1888594a4e76337aa01e88
for n in 03 05 02 04 06 01 07 08; do
  W=/home/claude/fz2 $R/judge_v6.sh $R/redteamE/d$n $R/results/Ed$n.txt
done
echo E_DONE
