import Mathlib

namespace Blind.ThomasFermi

open Set Filter Topology

theorem thomas_fermi_initial_slope (y : ℝ → ℝ) (d : ℝ)
    (hcont : ContinuousOn y (Ici 0))
    (hpos : ∀ x, 0 ≤ x → 0 < y x)
    (hdiff1 : DifferentiableOn ℝ y (Ioi 0))
    (hdiff2 : DifferentiableOn ℝ (deriv y) (Ioi 0))
    (hode : ∀ x, 0 < x → deriv (deriv y) x = (y x) ^ ((3 : ℝ) / 2) / Real.sqrt x)
    (h0 : y 0 = 1)
    (hinf : Tendsto y atTop (𝓝 0))
    (hd : HasDerivWithinAt y d (Ici 0) 0) :
    (-1.58807103 : ℝ) ≤ d ∧ d ≤ -1.58807102 := by
  sorry

end Blind.ThomasFermi
