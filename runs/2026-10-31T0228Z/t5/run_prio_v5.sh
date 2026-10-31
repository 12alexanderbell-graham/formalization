#!/bin/bash
# Priority queue for judge v5 (run 0228Z): red team D, the ports, the defects accepted before, then the rest.
H=/home/claude/formalization/runs/2026-10-31T0228Z/t5; O=/home/claude/formalization/runs/2026-10-31T0028Z/t5
R=$H/results; mkdir -p $R
pick(){ if [ -d $H/ports/$1 ]; then echo $H/ports/$1; elif [ ${1:0:1} = D ]; then echo $H/redteamD/${1:1}; else echo $O/redteam${1:0:1}/${1:1}; fi; }
for n in Dd01 Dd02 Dd03 Dd06 Dd07 Dd08 Ad06 Bd07 Bd07s Ad03 Dd04 Dd05 Ad05 Ad04 Bd04 Cd06 Cd02 Bd05 Ad07 Cd05 Cd04 Cd03 Cd07 Cd08 Cd01 Bd03 Bd06 Bd08 Bd02 Bd01 Ad02 Ad08r; do
  [ -f $R/$n.txt ] && continue
  $H/judge_v5.sh $(pick $n) $R/$n.txt
done
echo ALLDONE > $R/done
