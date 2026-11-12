#!/bin/sh
# Run 2026-11-12T2228Z: one certified chain (runs/2026-11-11T1228Z/scripts/gen_rev.py) for a row of rows_rev.json with
# every generator parameter explicit. usage: chain.sh tag mode(over|slow|tube) L h_den N digits OUTDIR
# (make_chains.sh = over 5 32 12 18, slow 17/4 32 12 18, tube 3/2 32 12 18). Tube chains with L != 3/2 need TubeRA
# (Checked/FSRev/RTubeA.lean, run 2026-11-12T2228Z).
# env W = the weights w1 w2 of the one-sided norm (default 1/2 2; row 04 tube: 2 8, amplification e^10 instead of e^18)
set -e
T=$1; M=$2; L=$3; HD=$4; N=$5; DG=$6; OUT=$7
J=runs/2026-11-12T2228Z/scripts/rows_rev.json
get() { python3 -c "import json;print(json.load(open('$J'))['$T']['$1'])"; }
G=runs/2026-11-11T1228Z/scripts/gen_rev.py
export FS_K=$(get K) FS_THETA=11/15 FS_HFINE=128:1/16
case $M in
  over) python3 $G $(get Aover) $L $HD $N $DG ${W:-1/2 2} over "$OUT/${T}_over.json" > "$OUT/${T}_over.log" 2>&1 ;;
  slow) python3 $G $(get Aslow) $L $HD $N $DG ${W:-1/2 2} slowL "$OUT/${T}_slow.json" > "$OUT/${T}_slow.log" 2>&1 ;;
  tube) FS_R0=$(get R0) python3 $G $(get Ac) $L $HD $N $DG ${W:-1/2 2} tube "$OUT/${T}_tube.json" > "$OUT/${T}_tube.log" 2>&1 ;;
esac
printf "%s %s L=%s h=1/%s N=%s D=%s: " $T $M $L $HD $N $DG; tail -1 "$OUT/${T}_$M.log" | grep -o "path margin.*\|AssertionError.*"
