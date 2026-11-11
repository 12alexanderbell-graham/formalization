#!/bin/sh
# Run 2026-11-11T1228Z: certified chains (exact rationals, Python) for the reversed-flow Falkner–Skan solution at
# β = −1988/10000 (scaled K = 2500/497, start (0, 0, A), A = √K · q(0); true A ≈ −0.0115670956, q(0) ≈ −0.0051574202):
#   Over  at A = −0.011567117 on [0, 17/4]  (p − 1 ≈ 1.5e-10 at the end)
#   SlowL at A = −0.011567073 on [0, 17/4]  (θ = 11/15; 3(1 − p) − q ≈ 4.3e-10, q ≈ 4e-11 at the end)
#   tube  around A = −0.011567095, radius 22/10⁹ (covers both ends), on [0, 3/2]
# Window q(0) ∈ (−0.00515743, −0.00515741) ⇔ A ∈ (−0.0115671176, −0.0115670728).
set -e
OUT=${1:-/tmp/claude-0/rev}
mkdir -p "$OUT"
G=runs/2026-11-11T1228Z/scripts/gen_rev.py
export FS_K=2500/497 FS_THETA=11/15 FS_HFINE=128:1/16
python3 $G -11567117/1000000000 17/4 32 12 18 1/2 2 over "$OUT/rover.json" > "$OUT/rover.log" 2>&1 &
python3 $G -11567073/1000000000 17/4 32 12 18 1/2 2 slowL "$OUT/rslow.json" > "$OUT/rslow.log" 2>&1 &
wait
FS_R0=22/1000000000 python3 $G -11567095/1000000000 3/2 32 12 18 1/2 2 tube "$OUT/rtube.json" > "$OUT/rtube.log" 2>&1
