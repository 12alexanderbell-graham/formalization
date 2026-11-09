#!/usr/bin/env python3
"""Run 2026-11-09T0428Z: promote the Falkner–Skan β = 1/10 row (copy of runs/2026-11-08T2028Z/scripts/promote_fsf.py with 5 -> 10) to Checked (pattern of
runs/2026-11-08T0428Z/scripts/promote_homann.py and runs/2026-11-08T1628Z/scripts/promote_hb.py):
Work/FSTenth/*.lean -> Checked/FSTenth/*.lean and Work/FalknerSkan/TenthBounded.lean ->
Checked/FalknerSkan/TenthBounded.lean; `Work.` -> `Checked.` in every name, `import Mathlib` replaced by
the specific Mathlib imports of the Checked module each file was ported from, module docs replaced by
number-free text. Statements and proofs otherwise byte-identical to Work."""
import re, pathlib
ROOT = pathlib.Path(__file__).resolve().parents[3]
def mlimports(path):
    return [l for l in (ROOT / path).read_text().splitlines() if l.startswith("import Mathlib.")]
SRC = {  # module -> (Checked module whose Mathlib imports it takes, number-free doc)
 "F10ExBase": ("Checked/Homann/HmExBase.lean", "the clamped coefficient-ten field and the two shooting events used by the existence argument"),
 "F10CellW": ("Checked/Homann/HmCellW.lean", "weighted one-sided validated cells for the coefficient-ten third-order system, every numeric side condition decided by kernel evaluation over the rationals"),
 "F10CellWC": ("Checked/Homann/HmCellWC.lean", "weighted one-sided validated cells for the clamped coefficient-ten field, with the clamp box checked on every cell"),
 "F10UData": ("Checked/Homann/HmUData.lean", "generated cells for the coefficient-ten initial-value problem started at the lower end of the window: the undershoot event"),
 "F10OData": ("Checked/Homann/HmOData.lean", "generated cells for the coefficient-ten initial-value problem started at the upper end of the window: the overshoot event"),
 "F10UDataC": ("Checked/Homann/HmUDataC.lean", "generated cells for the clamped coefficient-ten field started at the lower end of the window"),
 "F10ODataC": ("Checked/Homann/HmODataC.lean", "generated cells for the clamped coefficient-ten field started at the upper end of the window"),
 "F10ExFlow": ("Checked/Homann/HmExFlow.lean", "a global flow of the clamped coefficient-ten field, continuous in the wall value, with forward and backward uniqueness"),
 "F10ExLimit": ("Checked/Homann/HmExLimit.lean", "a flow with neither shooting event has a velocity profile tending to one"),
 "F10ExAssemble": ("Checked/Homann/HmExAssemble.lean", "the shooting argument: a solution of the coefficient-ten boundary-value problem with wall value inside the certified window"),
 "F10ExMono": ("Checked/Homann/HmExMono.lean", "the shooting solution has a positive second derivative on the closed half-line"),
 "F10IVP": ("Checked/Homann/HmIVP.lean", "along the certified cells the clamps are inactive, so at both ends of the window the clamped flow solves the coefficient-ten initial-value problem"),
 "FSTenth": ("Checked/Homann/Homann.lean", "the Falkner–Skan equation with pressure-gradient coefficient one tenth after the similarity scaling by the square root of that coefficient: the two certified shooting events and existence"),
 "F10Bounded": (None, "the coefficient-ten problem in the class where the velocity profile is bounded by one in absolute value: window, equality of two solutions and existence by the Crocco comparison and the shooting construction"),
}
F10B_IMPORTS = sorted(set(mlimports("Checked/FalknerSkan/MonotoneWindow.lean") + mlimports("Checked/FalknerSkan/MonotoneExists.lean")
                         + mlimports("Checked/FalknerSkan/Bounded.lean") + mlimports("Checked/FalknerSkan/BoundedTools.lean")))
def promote(src, dst, imports, doc, modname):
    s = (ROOT / src).read_text(encoding="utf-8")
    s = s.replace("import Work.Sim.OneSided3", "import Checked.Sim.OneSided3").replace("Work.", "Checked.")
    lines = s.split("\n")
    if lines[0] == "import Mathlib":
        s = "\n".join(imports + lines[1:])
    s, k = re.subn(r"/-!.*?-/", lambda m: f"/-! {doc}. Module `{modname}`, promoted from `{src}`. -/", s, count=1, flags=re.S)
    assert k == 1, src
    assert "Work." not in s and "sorry" not in s and "native_decide" not in s and "import Mathlib\n" not in s, src
    s = re.sub(r"(?m)^#print axioms.*\n", "", s)
    (ROOT / dst).parent.mkdir(parents=True, exist_ok=True)
    (ROOT / dst).write_text(s, encoding="utf-8")
for m, (ref, doc) in SRC.items():
    imps = mlimports(ref) if ref else F10B_IMPORTS
    promote(f"Work/FSTenth/{m}.lean", f"Checked/FSTenth/{m}.lean", imps, "Falkner–Skan one-tenth row, " + doc, m)
DOC = ("Falkner–Skan wedge flow with pressure-gradient coefficient one tenth: every solution of the boundary-value "
       "problem whose velocity profile is bounded by one in absolute value on the closed half-line has its wall shear "
       "inside the window of the statement, any two such solutions are equal on the closed half-line, and a solution "
       "with velocity profile in the half-open unit interval exists; obtained from the coefficient-ten theorems of "
       "`Checked.FSTenth.F10Bounded` by the similarity scaling of `Checked.FalknerSkan.FSScale`")
promote("Work/FalknerSkan/TenthBounded.lean", "Checked/FalknerSkan/TenthBounded.lean", [], DOC, "TenthBounded")
print("promoted")
