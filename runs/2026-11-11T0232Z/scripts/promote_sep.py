#!/usr/bin/env python3
"""Run 2026-11-11T0232Z: promote the Falkner–Skan separation pair (proved in Work this run) to Checked, pattern of
runs/2026-11-09T1028Z/scripts/promote_fsneg.py (imported, not copied): Work/FSSep/*.lean -> Checked/FSSep/*.lean,
Work/FalknerSkan/{Separation,SeparationUnique}.lean -> Checked/FalknerSkan/; `Work.` -> `Checked.`, `import Mathlib`
replaced by the specific Mathlib imports of the Checked Falkner–Skan modules, number-free module docs, `#print axioms`
lines dropped. Statements and proofs otherwise byte-identical to Work, except the uniqueness headline's name (no
strength word in names, PROMPT note on V13): fs_separation_unique -> fs_separation_beta_eq."""
import importlib.util, pathlib, re
ROOT = pathlib.Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("pf", ROOT / "runs/2026-11-09T1028Z/scripts/promote_fsneg.py")
src = (ROOT / "runs/2026-11-09T1028Z/scripts/promote_fsneg.py").read_text()
# reuse only the promote() function and IMPS, without running the old promotion
ns = {"__file__": str(ROOT / "runs/2026-11-09T1028Z/scripts/promote_fsneg.py")}
exec(src.split("for m, doc in FSNEG.items():")[0], ns)
promote = ns["promote"]
SEP = {
 "SBase": "the clamped field of the scaled adverse-sign problem with a free coefficient, the overshoot and slow-approach events from a zero wall value, and the certified chain shape",
 "SCellWC": "weighted one-sided validated cells for the clamped adverse-sign field with a rational coefficient, every numeric side condition decided by kernel evaluation over the rationals",
 "SOverLo": "generated cells for the clamped adverse-sign field from a zero wall value at the lower coefficient: the overshoot event",
 "SSlowHi": "generated cells for the clamped adverse-sign field from a zero wall value at the upper coefficient: the slow-approach event",
 "SFlow": "a global flow of the clamped adverse-sign field from a zero wall value, continuous in the coefficient, with forward and backward uniqueness",
 "SUnclamp": "a trajectory of the clamped field from a zero wall value that enters the slow-approach region, or has neither event, never meets a clamp",
 "SAssemble": "the shooting argument in the coefficient: openness and disjointness of the two event sets, a coefficient in neither, and the separation profile it gives",
 "UCrocco": "the Crocco map of the pressure-gradient form for a solution with positive second derivative on an open interval from the wall",
 "UCompare": "comparison of two zero-wall-value solutions with different pressure-gradient parameters in Crocco variables: order at the wall, no crossing, and the first step of the tail estimate",
 "UPair": "two zero-wall-value solutions with different pressure-gradient parameters cannot both exist when the one with the larger parameter approaches the edge value faster than every exponential",
}
FS = {
 "Separation": "Falkner–Skan separation: a pressure-gradient parameter with a zero-wall-shear solution approaching the edge value faster than every exponential",
 "SeparationUnique": "Falkner–Skan separation: two pressure-gradient parameters with zero-wall-shear solutions approaching the edge value faster than every exponential are equal",
}
for m, doc in SEP.items():
    promote(f"Work/FSSep/{m}.lean", f"Checked/FSSep/{m}.lean", "Falkner–Skan separation, " + doc, m)
for m, doc in FS.items():
    promote(f"Work/FalknerSkan/{m}.lean", f"Checked/FalknerSkan/{m}.lean", doc, m)
p = ROOT / "Checked/FalknerSkan/SeparationUnique.lean"
s = p.read_text(); assert s.count("theorem fs_separation_unique") == 1
p.write_text(s.replace("theorem fs_separation_unique", "theorem fs_separation_beta_eq"))
print("promoted", len(SEP) + len(FS))
