#!/usr/bin/env python3
"""Run 2026-11-09T0028Z: promote the unrestricted Falkner–Skan class to Checked.
Work/FalknerSkan/UnrestrictedCore.lean -> Checked/FalknerSkan/LimitCore.lean and
Work/FalknerSkan/Unrestricted.lean -> Checked/FalknerSkan/Limit.lean: `Work.` -> `Checked.`,
module docs replaced by number-free text, the phrase "with no bound assumed on p" dropped from the
headline docstrings (the generated claim states the hypotheses). Statements and proofs otherwise
byte-identical to Work."""
import re, pathlib
ROOT = pathlib.Path(__file__).resolve().parents[3]
DOCS = {
 "UnrestrictedCore": "Stagnation-point equations written as a first-order system with a real coefficient of the product term at least one: every solution on the closed half-line that starts at zero with velocity profile zero and whose velocity profile tends to one has positive second derivative on the closed half-line, so it lies in the class where the velocity profile is bounded by one in absolute value; weighted monotone quantities, the last zero of the second derivative, and backward uniqueness against a straight line",
 "Unrestricted": "Falkner–Skan and stagnation-point boundary-value problems without any bound on the velocity profile: for a pressure-gradient coefficient in the half-open unit interval every solution has positive second derivative, and the window and equality theorems of the class bounded by one in absolute value hold for every solution of the boundary-value problem",
}
NEW = {"UnrestrictedCore": "LimitCore", "Unrestricted": "Limit"}
for m, doc in DOCS.items():
    src = ROOT / f"Work/FalknerSkan/{m}.lean"
    s = src.read_text(encoding="utf-8").replace("Work.", "Checked.")
    # Checked module names: "Unrestricted" is a generality word (check_claim_vocab V13 rejected it,
    # rightly); the modules are named after the only class condition left, the limit p -> 1.
    s = s.replace("Checked.FalknerSkan.UnrestrictedCore", "Checked.FalknerSkan.LimitCore").replace(
        "Checked.FalknerSkan.Unrestricted", "Checked.FalknerSkan.Limit")
    s = s.replace("Module `UnrestrictedCore`", "Module `LimitCore`")
    s, k = re.subn(r"/-!.*?-/", lambda _: f"/-! {doc}. Module `{m}`, promoted from `Work/FalknerSkan/{m}.lean`. -/", s, count=1, flags=re.S)
    assert k == 1
    s = s.replace(", with no bound assumed on p,", "").replace(", with no bound assumed on p:", ":")
    assert "no bound" not in s.split("-/", 1)[1], m
    assert "sorry" not in s and "native_decide" not in s and "import Mathlib\n" not in s and "Work." not in s
    s = re.sub(r"(?m)^#print axioms.*\n", "", s)
    s = s.replace(f"Module `{m}`,", f"Module `{NEW[m]}`,")
    (ROOT / f"Checked/FalknerSkan/{NEW[m]}.lean").write_text(s, encoding="utf-8")
print("promoted")
