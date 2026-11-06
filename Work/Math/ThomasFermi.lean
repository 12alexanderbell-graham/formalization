import Mathlib

/-!
# Thomas–Fermi equation: initial slope of the neutral-atom solution

The dimensionless Thomas–Fermi equation of the neutral atom: y'' = y^{3/2} / √x for x > 0,
y(0) = 1, y(x) → 0 as x → ∞, with y > 0 on [0, ∞). The initial slope y'(0) of this solution
fixes the Thomas–Fermi energy of neutral atoms. Digits of y'(0) in the literature come from
floating-point computations; this file states a certified enclosure.

Conventions: y and φ are real functions on ℝ (values for x < 0 are never used); φ is the
derivative of y on [0, ∞) (a right derivative at 0) and is continuous at 0 from the right;
y^{3/2} is the real power `y x ^ (3 / 2 : ℝ)` (y x > 0 by hypothesis).

Statement: every such solution has −1.58807103 ≤ y'(0) ≤ −1.58807102.
-/

namespace Work.Math.ThomasFermi
open Set Filter Topology

/-- Every solution y of the Thomas–Fermi equation y'' = y^{3/2}/√x on (0, ∞) with y' = φ on
[0, ∞), φ continuous at 0 from the right, y(0) = 1, y > 0 on [0, ∞) and y(x) → 0 as x → ∞ has
initial slope −1.58807103 ≤ φ(0) ≤ −1.58807102. -/
theorem tf_initial_slope (y φ : ℝ → ℝ)
    (hy : ∀ x, 0 ≤ x → HasDerivWithinAt y (φ x) (Ici 0) x)
    (hφ : ∀ x, 0 < x → HasDerivAt φ (y x ^ ((3 : ℝ) / 2) / Real.sqrt x) x)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (h0 : y 0 = 1) (hpos : ∀ x, 0 ≤ x → 0 < y x)
    (hlim : Tendsto y atTop (𝓝 0)) :
    -1.58807103 ≤ φ 0 ∧ φ 0 ≤ -1.58807102 := by
  sorry

end Work.Math.ThomasFermi
