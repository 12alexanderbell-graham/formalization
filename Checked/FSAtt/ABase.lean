import Checked.FSSep.SBase

/-! Falkner–Skan adverse pressure gradient with a free scaled coefficient and a positive wall value: the slow-approach event with the threshold valid for every coefficient at least five, and the certified chain shape from a start with zero position and velocity. Module `ABase`, promoted from `Work/FSAtt/ABase.lean`. -/

namespace Checked.FSAtt.ABase
open Set Checked.FSNeg.NBase Checked.FSSep.SBase

/-- Slow: at some η > 0 the trajectory is in the region 0 ≤ p < 1, 0 < q < 3(1 − p), f > 11/15,
having had p < 1 and q > 0 on [0, η]. -/
def SlowA (Y : ℝ → ℝ × ℝ × ℝ) : Prop :=
  ∃ η > 0, (∀ s ∈ Icc 0 η, (Y s).2.1 < 1 ∧ 0 < (Y s).2.2) ∧
    0 ≤ (Y η).2.1 ∧ (Y η).2.2 < 3 * (1 - (Y η).2.1) ∧ 11 / 15 < (Y η).1

/-- The certified chain shape: every solution of the clamped coefficient-K field on [0, T] from
(0, 0, α) has the event `E`. -/
def ChainA (K α : ℝ) (E : (ℝ → ℝ × ℝ × ℝ) → Prop) : Prop :=
  ∃ T > 0, ∀ Y : ℝ → ℝ × ℝ × ℝ, (∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vS K t (Y t)) (Icc 0 T) t) →
    Y 0 = (0, 0, α) → E Y

end Checked.FSAtt.ABase
