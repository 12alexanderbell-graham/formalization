#!/bin/sh
# Run 2026-11-11T0828Z: certified event chains (exact rationals, Python) for the β = −1988/10000 window,
# scaled K = 1/|β| = 2500/497, start (0, 0, A), A = √K · q(0). Window q(0) ∈ (0.0052181, 0.0052182) ⇔
# A ∈ (0.0117031887, 0.0117034130); true A ≈ 0.0117033858.
#   Slow (θ = 11/15, the K ≥ 5 threshold of Checked/FSSep/SBase.lean) at A = 0.011703189 on [0, 4]:
#     h = 1/128 on [0, 1/16) then 1/32, degree 12, 10^-18 → 134 cells, path margin 4.9e-10, end margin 3.6e-9  OK
#   Over at A = 0.0117034 on [0, 17/4]: same steps → 142 cells, end margin 9.6e-11  OK
# The emitter (runs/2026-11-09T0828Z/scripts/emit_neg_wc.py) and the Lean stack Checked/FSNeg/* hard-code K = 10,
# Slow's 11/30 and the class bound α ≤ 11/10: template them first (STATE exact next step 2).
set -e
OUT=${1:-/tmp/fs1988}
mkdir -p "$OUT"
G=runs/2026-11-11T0828Z/scripts/gen_neg_wc_theta.py
FS_HFINE=128:1/16 FS_K=2500/497 FS_THETA=11/15 python3 $G 11703189/1000000000 4 32 12 18 1/2 2 slow "$OUT/lo.json"
FS_HFINE=128:1/16 FS_K=2500/497 FS_THETA=11/15 python3 $G 117034/10000000 17/4 32 12 18 1/2 2 over "$OUT/hi.json"
