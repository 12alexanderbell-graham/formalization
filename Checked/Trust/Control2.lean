import Mathlib.Data.Real.Basic

/-! CONTROL (branch `control/unpinned-and-hidden` only, run 2228Z). CI must fail at the trust-map
step with two errors:
1. `uses_unpinned` rests on `fakeDist`, a PHYSICS definition without a pin;
2. `hidden_vacuous` is vacuous with its hypotheses hidden behind a definition
   (adversarial review item 1); no witness can exist. -/

namespace Checked.Trust.Control2

/-- A wrong "distance" (deliberately unpinned). -/
def fakeDist (z : ℝ) : ℝ := z ^ 2

theorem uses_unpinned : fakeDist 0 = 0 := by simp [fakeDist]

/-- Hypotheses hidden behind a definition. -/
def HiddenClaim : Prop := ∀ x : ℝ, x < x → x = 7

theorem hidden_vacuous : HiddenClaim := fun x h => absurd h (lt_irrefl x)

end Checked.Trust.Control2
