#!/usr/bin/env python3
"""Run 2026-11-09T1028Z: promote the Falkner–Skan β < 0 stack (run 2026-11-09T0828Z, proved in Work) to Checked
(pattern of runs/2026-11-09T0428Z/scripts/promote_fst.py): Work/FSNeg/*.lean -> Checked/FSNeg/*.lean and
Work/FalknerSkan/{NegCrocco,NegNoCross,NegUPrime,NegCore,NegDecay,NegTenth,NegOutside}.lean -> Checked/FalknerSkan/;
`Work.` -> `Checked.` in every name, `import Mathlib` replaced by the union of the specific Mathlib imports of the
Checked Falkner–Skan modules (Checked/FSTenth/*, Checked/FalknerSkan/*: no module outside the existing Checked
import closure), module docs replaced by number-free text, `#print axioms` lines dropped. Statements and proofs
otherwise byte-identical to Work."""
import re, pathlib
ROOT = pathlib.Path(__file__).resolve().parents[3]
IMPS = sorted({l for p in list((ROOT / "Checked/FSTenth").glob("*.lean")) + list((ROOT / "Checked/FalknerSkan").glob("*.lean"))
               for l in p.read_text().splitlines() if l.startswith("import Mathlib.")})
FSNEG = {
 "NBase": "the clamped field of the scaled adverse-sign problem and the two shooting events (slow approach and overshoot)",
 "NCellWC": "weighted one-sided validated cells for the clamped adverse-sign field, every numeric side condition decided by kernel evaluation over the rationals, with the clamp box checked on every cell",
 "NSlowHalf": "generated cells for the clamped adverse-sign field started at the lower test value: the slow-approach event",
 "NSlow34": "generated cells for the clamped adverse-sign field started at the middle test value: the slow-approach event",
 "NOver11": "generated cells for the clamped adverse-sign field started at the upper test value: the overshoot event",
 "NFlow": "a global flow of the clamped adverse-sign field, continuous in the wall value, with forward and backward uniqueness",
 "NLemma1": "elementary sign facts for the scaled adverse-pressure system, with no sign condition on its coefficient",
 "NSlowInv": "forward invariance of the slow-approach region of the scaled adverse-pressure system",
 "NLimit": "a solution with positive second derivative and velocity profile below the edge value on a half-line has its profile tending to the edge value, and then the stream function grows without bound",
 "NRiccati": "a lower bound of the second derivative by a positive multiple of the velocity defect on a half-line, with an unbounded stream function, upgrades to a bound by every multiple eventually",
 "NUnclamp": "a slow-approach trajectory of the clamped field never meets a clamp, so it solves the unclamped problem",
 "NAssemble": "the shooting argument on the scaled adverse-sign problem: openness and disjointness of the two event sets, a wall value in neither, and the solution it gives",
}
FS = {
 "NegCrocco": "the Crocco map for the adverse pressure sign",
 "NegNoCross": "no crossing of two Crocco curves of the scaled adverse-pressure system, and the first steps of the wall-shear comparison",
 "NegUPrime": "the solution approaching the edge value faster than every exponential has the largest wall shear, in the scaled system",
 "NegCore": "the similarity scaling between the adverse-sign Falkner–Skan equation and its scaled form, and forward uniqueness of the initial-value problem",
 "NegDecay": "Falkner–Skan with adverse pressure gradient: in the class of solutions with positive second derivative that approach the edge value faster than every exponential, the wall shear is the largest and two solutions are equal",
 "NegTenth": "Falkner–Skan with the adverse pressure-gradient coefficient of minus one tenth: existence in the fast-approach class, and two solutions with different wall shear outside it",
 "NegOutside": "Falkner–Skan with the adverse pressure-gradient coefficient of minus one tenth: two solutions with different wall shear, neither in the fast-approach class",
}
def promote(src, dst, doc, modname):
    s = (ROOT / src).read_text(encoding="utf-8")
    s = s.replace("import Work.Sim.OneSided3", "import Checked.Sim.OneSided3").replace("Work.", "Checked.")
    lines = s.split("\n")
    if "import Mathlib" in lines:
        i = lines.index("import Mathlib")
        rest = [l for l in lines if l != "import Mathlib" and not (l.startswith("import Mathlib.") and l in IMPS)]
        s = "\n".join(rest[:i] + IMPS + rest[i:])
    s, k = re.subn(r"/-!.*?-/", lambda m: f"/-! {doc}. Module `{modname}`, promoted from `{src}`. -/", s, count=1, flags=re.S)
    assert k == 1, src
    head, sep, tail = s.partition("-/")
    tail = re.sub(r"/-!.*?-/", f"/-! {doc} (continued). -/", tail, flags=re.S)
    s = head + sep + tail
    assert "Work." not in s and "sorry" not in s and "native_decide" not in s and "import Mathlib\n" not in s, src
    s = re.sub(r"(?m)^#print axioms.*\n", "", s)
    (ROOT / dst).parent.mkdir(parents=True, exist_ok=True)
    (ROOT / dst).write_text(s, encoding="utf-8")
for m, doc in FSNEG.items():
    promote(f"Work/FSNeg/{m}.lean", f"Checked/FSNeg/{m}.lean", "Falkner–Skan adverse pressure gradient, " + doc, m)
for m, doc in FS.items():
    promote(f"Work/FalknerSkan/{m}.lean", f"Checked/FalknerSkan/{m}.lean", doc, m)
print("promoted", len(FSNEG) + len(FS))
