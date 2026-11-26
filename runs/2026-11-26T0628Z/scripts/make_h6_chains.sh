#!/bin/sh
# Run 2026-11-26T0628Z: certified exact-rational chains at beta = -19/200 (K = 200/19) for the hypothesis-6 witness
# of fs_neg_decay_max_shear: reversed-flow over (L = 5), slowL (L = 17/4), tube (L = 3/2, step 1/128) with
# runs/2026-11-11T1228Z/scripts/gen_rev.py; attached slow (SlowA, A = 1063/1000) and over (A = 107/100) with
# runs/2026-11-11T0828Z/scripts/gen_neg_wc_theta.py.
set -e
OUT=runs/2026-11-26T0628Z/cells; J=runs/2026-11-26T0628Z/scripts/rows_h6.json
get() { python3 -c "import json;print(json.load(open('$J'))['095']['$1'])"; }
G=runs/2026-11-11T1228Z/scripts/gen_rev.py; GA=runs/2026-11-11T0828Z/scripts/gen_neg_wc_theta.py
export FS_K=200/19 FS_THETA=11/15 FS_HFINE=128:1/16
python3 $G $(get Aover) 5 32 12 18 1/2 2 over "$OUT/rev_over.json" > "$OUT/rev_over.log" 2>&1 &
python3 $G $(get Aslow) 17/4 32 12 18 1/2 2 slowL "$OUT/rev_slow.json" > "$OUT/rev_slow.log" 2>&1 &
FS_R0=$(get R0) python3 $G $(get Ac) 3/2 128 12 18 1/2 2 tube "$OUT/rev_tube.json" > "$OUT/rev_tube.log" 2>&1 &
python3 $GA $(get Alo) 4 32 12 18 1/2 2 slow "$OUT/att_slow.json" > "$OUT/att_slow.log" 2>&1 &
python3 $GA $(get Ahi) 5 32 12 18 1/2 2 over "$OUT/att_over.json" > "$OUT/att_over.log" 2>&1 &
wait
for m in rev_over rev_slow rev_tube att_slow att_over; do printf "%s: " $m; tail -1 "$OUT/$m.log" | cut -c1-200; done
