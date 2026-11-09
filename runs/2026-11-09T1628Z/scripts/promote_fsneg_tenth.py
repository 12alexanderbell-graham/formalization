#!/usr/bin/env python3
"""Run 2026-11-09T1628Z: promote the Falkner–Skan β = −1/10 window and reversed-flow theorems (run 2026-11-09T1228Z,
proved in Work, CI work job of 9f7db47 green) to Checked. Pattern and copy rules of
runs/2026-11-09T1028Z/scripts/promote_fsneg.py (imported, not duplicated): `Work.` -> `Checked.`, `import Mathlib`
replaced by the specific Mathlib imports of the Checked Falkner–Skan modules, module docs replaced by number-free
text, `#print axioms` lines dropped. Statements and proofs otherwise byte-identical to Work."""
import importlib.util, pathlib, sys
ROOT = pathlib.Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("p1028", ROOT / "runs/2026-11-09T1028Z/scripts/promote_fsneg.py")
src = (ROOT / "runs/2026-11-09T1028Z/scripts/promote_fsneg.py").read_text(encoding="utf-8")
# reuse only the definitions (IMPS, promote), not the run-1028Z module loop
ns = {"__file__": str(ROOT / "runs/2026-11-09T1028Z/scripts/promote_fsneg.py")}
exec(src.split("for m, doc in FSNEG.items():")[0], ns)
promote = ns["promote"]
FSNEG = {
 "NWinLo": "generated cells for the clamped adverse-sign field started at the lower end of the narrow wall-value interval: the slow-approach event",
 "NWinHi": "generated cells for the clamped adverse-sign field started at the upper end of the narrow wall-value interval: the overshoot event",
 "NWindow": "the shooting argument for any certified pair of wall values, the square-root enclosures of the similarity scaling, and the wall-shear interval of the decay-class solution",
 "LCell": "validated cells for the clamped adverse-sign field below zero wall shear: cell boxes, sign side conditions, end states and the lower slow-approach event",
 "LInv": "forward invariance of the lower slow-approach region of the clamped adverse-sign field",
 "LUnclamp": "a lower slow-approach trajectory with velocity profile at most the edge value never meets a clamp after the tube time, so it solves the unclamped problem",
 "LAssemble": "the shooting argument on the reversed-flow branch: openness and disjointness of the two event sets, a wall value in neither, and the solution it gives",
 "LOver": "generated cells for the clamped adverse-sign field started at the lower end of the reversed-flow interval: the overshoot event",
 "LSlow": "generated cells for the clamped adverse-sign field started at the upper end of the reversed-flow interval: the lower slow-approach event",
 "LTube": "generated cells for the clamped adverse-sign field started in a small ball around the reversed-flow interval: every trajectory of the interval stays inside the clamps up to the tube time",
}
FS = {
 "NegWindow": "Falkner–Skan with the adverse pressure-gradient coefficient of minus one tenth: the wall shear of every solution with positive second derivative that approaches the edge value faster than every exponential, and an upper bound for every solution with positive second derivative",
 "NegReversed": "Falkner–Skan with the adverse pressure-gradient coefficient of minus one tenth: a solution with negative wall shear that approaches the edge value faster than every exponential, and solutions with different wall shear in that class",
}
for m, doc in FSNEG.items():
    promote(f"Work/FSNeg/{m}.lean", f"Checked/FSNeg/{m}.lean", "Falkner–Skan adverse pressure gradient, " + doc, m)
for m, doc in FS.items():
    promote(f"Work/FalknerSkan/{m}.lean", f"Checked/FalknerSkan/{m}.lean", doc, m)
print("promoted", len(FSNEG) + len(FS))
