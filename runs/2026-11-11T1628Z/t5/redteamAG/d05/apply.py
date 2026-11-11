import sys, os
root = sys.argv[1]
def w(rel, text):
    p = os.path.join(root, rel)
    os.makedirs(os.path.dirname(p), exist_ok=True)
    assert not os.path.exists(p), rel
    open(p, "w").write(text)
def append(rel, text):
    p = os.path.join(root, rel)
    s = open(p).read()
    if not s.endswith("\n"): s += "\n"
    open(p, "w").write(s + text)

HEAD = r'''import Checked.Cosmography.LCDMCoefficients

/-! A unique stationary point of the scale factor's logarithm (zero of the Hubble rate). -/

namespace Checked.AGWrap.D05

open Checked.Cosmography

/-- If the Hubble rate has exactly one zero, it has a zero. -/
theorem hubble_zero_exists (a : ℝ → ℝ) (h : ∃! t : ℝ, hubble a t = 0) :
    ∃ t : ℝ, hubble a t = 0 :=
  h.exists

end Checked.AGWrap.D05

#print axioms Checked.AGWrap.D05.hubble_zero_exists
'''
WIT = r'''import Checked.Trust.NonVacuity
import Checked.AGWrap.D05
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace Checked.Trust.AGW05

open Checked.Cosmography

theorem hubble_zero_exists : nonvacuity% Checked.AGWrap.D05.hubble_zero_exists :=
  ⟨fun t => t, ExistsUnique.intro 0 (by simp [hubble])
    (fun y hy => by simpa [hubble] using hy), trivial⟩

theorem hubble_zero_exists_h1 : necessity% Checked.AGWrap.D05.hubble_zero_exists 1 :=
  ⟨Real.exp, by
    rintro ⟨t, ht⟩
    simp [hubble, Real.deriv_exp] at ht⟩

end Checked.Trust.AGW05
'''
w("Checked/AGWrap/D05.lean", HEAD)
w("Checked/Trust/AGW05.lean", WIT)
append("Checked.lean", "import Checked.AGWrap.D05\nimport Checked.Trust.AGW05\n")
append("scripts/trust/headlines.txt", "Checked.AGWrap.D05.hubble_zero_exists\n")
