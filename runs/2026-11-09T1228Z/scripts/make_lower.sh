#!/bin/sh
# Run 2026-11-09T1228Z: certified chains for the reversed-flow (lower) Falkner–Skan beta = -1/10 solution
# (scaled K = 10, adverse sign; window -0.4444461497 .. -0.4444461493, research note 0428Z §3.3):
#   Over  at A = -0.4444461497 on [0, 15/4]      (h = 1/32, degree 12, 10^-18)
#   SlowL at A = -0.4444461493 on [0, 4]
#   tube  around A = -0.4444461495, radius 2e-10, on [0, 3/2]: inside the clamps, p > -1/2, end state
set -e
OUT=$1; DST=$2
G=runs/2026-11-09T1228Z/scripts/gen_low.py
E=runs/2026-11-09T1228Z/scripts/emit_low.py
FS_K=10 python3 $G -4444461497/10000000000 15/4 32 12 18 1/2 2 over "$OUT/lover.json"
FS_K=10 python3 $G -4444461493/10000000000 4 32 12 18 1/2 2 slowL "$OUT/lslow.json"
FS_R0=1/5000000000 FS_K=10 python3 $G -4444461495/10000000000 3/2 32 12 18 1/2 2 tube "$OUT/ltube.json"
python3 $E "$OUT/lover.json" 10 "$DST/LOver.lean" LOver "-4444461497 / 10000000000"
python3 $E "$OUT/lslow.json" 10 "$DST/LSlow.lean" LSlow "-4444461493 / 10000000000"
python3 $E "$OUT/ltube.json" 10 "$DST/LTube.lean" LTube "-4444461495 / 10000000000" 1/5000000000
