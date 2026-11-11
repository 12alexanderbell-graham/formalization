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

/-! Sign of the Hubble rate from an inverse relation with a non-negative coefficient. -/

namespace Checked.AGWrap.D03

open Checked.Cosmography

/-- If `c * H(t₀) = 1` for a non-negative real `c`, the Hubble rate at `t₀` is positive. -/
theorem hubble_pos_of_inverse (a : ℝ → ℝ) (t₀ : ℝ) (c : NNReal)
    (hc : (c : ℝ) * hubble a t₀ = 1) : 0 < hubble a t₀ := by
  have h0 : (0 : ℝ) ≤ (c : ℝ) := NNReal.coe_nonneg c
  have hne : hubble a t₀ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hc
    exact zero_ne_one hc
  rcases lt_or_gt_of_ne hne with h | h
  · exfalso
    nlinarith [mul_nonneg h0 (neg_nonneg.mpr h.le)]
  · exact h

end Checked.AGWrap.D03

#print axioms Checked.AGWrap.D03.hubble_pos_of_inverse
'''
WIT = r'''import Checked.Trust.NonVacuity
import Checked.AGWrap.D03
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace Checked.Trust.AGW03

open Checked.Cosmography

theorem hubble_pos_of_inverse : nonvacuity% Checked.AGWrap.D03.hubble_pos_of_inverse :=
  ⟨Real.exp, 0, 1, by simp [hubble, Real.deriv_exp], trivial⟩

theorem hubble_pos_of_inverse_h1 : necessity% Checked.AGWrap.D03.hubble_pos_of_inverse 1 :=
  ⟨fun _ => 0, 0, 0, by simp [hubble]⟩

end Checked.Trust.AGW03
'''
w("Checked/AGWrap/D03.lean", HEAD)
w("Checked/Trust/AGW03.lean", WIT)
append("Checked.lean", "import Checked.AGWrap.D03\nimport Checked.Trust.AGW03\n")
append("scripts/trust/headlines.txt", "Checked.AGWrap.D03.hubble_pos_of_inverse\n")
