#!/bin/bash
# red team F: before (checks of 7221e29, judge v6) and after (checks of 924a9d6, judge v7)
R=/home/claude/formalization/runs/2026-11-04T0428Z/t5
export W=/home/claude/fz2
cd $W && git checkout -q --detach 7221e29ae48f142572ebe569881630eabc63be32
$R/judge_v6_local.sh NONE $R/results/before_control.txt
for n in 03 05 07 08; do $R/judge_md.sh v6 $R/redteamF/d$n $R/results/before_Fd$n.txt; done
$R/judge_v6_local.sh $R/combinedLean $R/results/before_Fd01_02_04_06.txt
cd $W && git checkout -q --detach 924a9d6b52629e99ad31e771ea08878304c02c0b
$R/judge_v7.sh NONE $R/results/after_control.txt
for n in 03 05 07 08; do $R/judge_md.sh v7 $R/redteamF/d$n $R/results/after_Fd$n.txt; done
$R/judge_v7.sh $R/combinedLean $R/results/after_Fd01_02_04_06.txt
echo F_DONE
