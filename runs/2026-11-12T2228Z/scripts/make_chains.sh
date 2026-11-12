#!/bin/sh
# Run 2026-11-12T2228Z (copy of runs/2026-11-12T1828Z/scripts/make_chains.sh, rows file changed): certified exact-rational chains (runs/2026-11-11T1228Z/scripts/gen_rev.py) for the reversed-flow
# Falkner–Skan rows of rows_rev.json: over (L = 5), slowL (L = 17/4), tube (radius R0 around the centre, L = 3/2).
# usage: make_chains.sh tag OUTDIR [Lover] [Lslow]   (used: rows 15, 17 with defaults; rows 18, 19 with Lslow = 5, the slow chain at 17/4 failed its end condition by 2e-11 / 5e-11)
# Run 2026-11-12T2228Z: env SN, SD = Taylor degree and coefficient digits of the slow chain (row 09: SN=14 SD=22; at 12/18 its end condition failed by 9e-14)
set -e
T=$1; OUT=$2; LO=${3:-5}; LS=${4:-17/4}
J=runs/2026-11-12T2228Z/scripts/rows_rev.json
get() { python3 -c "import json;print(json.load(open('$J'))['$T']['$1'])"; }
G=runs/2026-11-11T1228Z/scripts/gen_rev.py
export FS_K=$(get K) FS_THETA=11/15 FS_HFINE=128:1/16
python3 $G $(get Aover) $LO 32 12 18 1/2 2 over "$OUT/${T}_over.json" > "$OUT/${T}_over.log" 2>&1
python3 $G $(get Aslow) $LS 32 ${SN:-12} ${SD:-18} 1/2 2 slowL "$OUT/${T}_slow.json" > "$OUT/${T}_slow.log" 2>&1
FS_R0=$(get R0) python3 $G $(get Ac) 3/2 32 12 18 1/2 2 tube "$OUT/${T}_tube.json" > "$OUT/${T}_tube.log" 2>&1
for m in over slow tube; do printf "%s %s: " $T $m; tail -1 "$OUT/${T}_$m.log" | grep -o "path margin.*"; done
