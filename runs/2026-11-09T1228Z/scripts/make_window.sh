#!/bin/sh
# Run 2026-11-09T1228Z: certified event chains for the ten-decimal window of the attached Falkner–Skan
# beta = -1/10 solution (scaled K = 10, adverse sign), generator and emitter of run 2026-11-09T0828Z unchanged.
#   Slow at A = 1.009619629 on [0, 3]:  h = 1/32, degree 12, coefficients 10^-18 (96 cells)
#   Over at A = 1.0096196292 on [0, 11/4]: h = 1/16, degree 16, coefficients 10^-18 (44 cells)
set -e
OUT=${1:-/tmp/fswin}
mkdir -p "$OUT"
G=runs/2026-11-09T0828Z/scripts/gen_neg_wc.py
E=runs/2026-11-09T0828Z/scripts/emit_neg_wc.py
FS_K=10 python3 $G 1009619629/1000000000 3 32 12 18 1/2 2 slow "$OUT/winlo.json"
FS_K=10 python3 $G 2524049073/2500000000 11/4 16 16 18 1/2 2 over "$OUT/winhi.json"
python3 $E "$OUT/winlo.json" 8 "$2/NWinLo.lean" NWinLo "1009619629 / 1000000000"
python3 $E "$OUT/winhi.json" 8 "$2/NWinHi.lean" NWinHi "2524049073 / 2500000000"
