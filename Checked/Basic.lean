import Mathlib.Tactic.Ring

/-!
# Placeholder

Exists only so the `Checked` library builds and the CI judge can be tested.
Remove when the first real result is promoted.
-/

namespace Checked

theorem placeholder (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

end Checked

namespace Checked
/-- Positive control: must make CI fail. -/
theorem control_false_claim : (1 : ℕ) = 2 := by
  sorry
end Checked
