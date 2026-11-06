import Mathlib

/-!
# Thomas–Fermi equation: existence of the neutral-atom solution

Companion of `Work.Math.ThomasFermi.tf_initial_slope` (non-vacuity): there is a pair (y, φ)
meeting every hypothesis of that theorem — y' = φ on [0, ∞) (a right derivative at 0), φ
continuous at 0 from the right, φ' = y^{3/2}/√x on (0, ∞), y(0) = 1, y > 0 on [0, ∞) and
y(x) → 0 as x → ∞.

Conventions as in `Work.Math.ThomasFermi`: y^{3/2} is the real power `y x ^ (3 / 2 : ℝ)`.
-/

namespace Work.Math.ThomasFermiExists
open Set Filter Topology

/-- There is a solution y of the Thomas–Fermi equation y'' = y^{3/2}/√x on (0, ∞) with y' = φ on
[0, ∞), φ continuous at 0 from the right, y(0) = 1, y > 0 on [0, ∞) and y(x) → 0 as x → ∞. -/
theorem tf_exists : ∃ y φ : ℝ → ℝ,
    (∀ x, 0 ≤ x → HasDerivWithinAt y (φ x) (Ici 0) x) ∧
    (∀ x, 0 < x → HasDerivAt φ (y x ^ ((3 : ℝ) / 2) / Real.sqrt x) x) ∧
    ContinuousWithinAt φ (Ici 0) 0 ∧ y 0 = 1 ∧ (∀ x, 0 ≤ x → 0 < y x) ∧
    Tendsto y atTop (𝓝 0) := by
  sorry

end Work.Math.ThomasFermiExists
