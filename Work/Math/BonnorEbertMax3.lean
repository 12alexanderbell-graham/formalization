import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Checked.Math.BEOMain
import Work.Math.BE3Main

/-! Bonnor–Ebert sphere, `BonnorEbertMax3` (FROZEN by run 2026-11-14T1828Z before proof).

Same setting and conventions as `Checked/Math/BonnorEbert.lean`, `BonnorEbertMax.lean`, `BonnorEbertMin.lean`,
`BonnorEbertMax2.lean` and `BonnorEbertMin2.lean`: the isothermal (Emden–Chandrasekhar) equation
w'' + (2/s) w' + e^w = 0 for w = −ψ (ρ = ρ_c e^{−ψ}), w(0) = 0, φ = w' with one-sided derivatives on [0, S] and
φ continuous at 0; the pressure-confined dimensionless mass m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π); the
centre-to-edge density contrast e^{−w(s)}.

The audited headlines `bonnor_ebert_max`, `bonnor_ebert_min`, `bonnor_ebert_second_max` and
`bonnor_ebert_second_min` give the first four extrema of the mass along the spiral. This file states the next
turn: beyond the second minimum ξ₄ ≈ 7850 the mass rises to a third maximum at a radius ξ₅ ≈ 84506 (density
contrast ≈ 3.557 · 10⁹), and that maximum is the strict maximum of the mass over every radius from ξ₄ to S
(any S at least 300000). Physically: every pressure-confined isothermal sphere at least as centrally condensed
as the second-minimum sphere has a dimensionless mass between m(ξ₄) ≈ 0.787994 and m(ξ₅) ≈ 0.800912, the upper
end attained exactly once.

Windows from the exact-rational one-sided-cell generator (`runs/2026-11-14T1828Z/scripts/gen_b3.py`) and a
float study (`runs/2026-11-14T1828Z/study/max3.py`, scipy rtol 1e-13; unchecked prose): ξ₅ ≈ 84506.33,
m(ξ₅) ≈ 0.80091195, e^{−w(ξ₅)} ≈ 3.55716 · 10⁹. -/

namespace Work.Math.BonnorEbertMax3
open Set

/-- Bonnor–Ebert sphere, the third maximum of the mass: for every S ≥ 300000 and every solution w of
w'' + (2/s)w' + e^w = 0 on (0, S] with w(0) = 0, w differentiable on [0, S] with derivative φ and φ continuous
at 0, with m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π), there are radii ξ₁ ∈ [6.4507514, 6.4507515],
ξ₂ ∈ [67.0075, 67.0076], ξ₃ ∈ [733.5, 734], ξ₄ ∈ [7849.5, 7849.75] and ξ₅ ∈ [84497, 84516] such that
m(s) < m(ξ₁) for every other s in [0, S], m(ξ₂) < m(s) for every other s in [ξ₁, S], m(s) < m(ξ₃) for every
other s in [ξ₂, S], m(ξ₄) < m(s) for every other s in [ξ₃, S], m(s) < m(ξ₅) for every other s in [ξ₄, S],
m(ξ₅) lies between 0.80091 and 0.800916, and the density contrast e^{−w(ξ₅)} lies between 3556300000 and
3558000000. -/
theorem bonnor_ebert_third_max (S : ℝ) (hS : 300000 ≤ S) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    (h0 : w 0 = 0) :
    ∃ ξ₁ ξ₂ ξ₃ ξ₄ ξ₅ : ℝ, 6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧ 67.0075 ≤ ξ₂ ∧ ξ₂ ≤ 67.0076 ∧
      733.5 ≤ ξ₃ ∧ ξ₃ ≤ 734 ∧ 7849.5 ≤ ξ₄ ∧ ξ₄ ≤ 7849.75 ∧ 84497 ≤ ξ₅ ∧ ξ₅ ≤ 84516 ∧
      (∀ s ∈ Icc (0 : ℝ) S, s ≠ ξ₁ →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ₁ ^ 2 * (-φ ξ₁) * Real.exp (w ξ₁ / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ s ∈ Icc ξ₁ S, s ≠ ξ₂ →
        ξ₂ ^ 2 * (-φ ξ₂) * Real.exp (w ξ₂ / 2) / Real.sqrt (4 * Real.pi) <
          s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ s ∈ Icc ξ₂ S, s ≠ ξ₃ →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ₃ ^ 2 * (-φ ξ₃) * Real.exp (w ξ₃ / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ s ∈ Icc ξ₃ S, s ≠ ξ₄ →
        ξ₄ ^ 2 * (-φ ξ₄) * Real.exp (w ξ₄ / 2) / Real.sqrt (4 * Real.pi) <
          s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ s ∈ Icc ξ₄ S, s ≠ ξ₅ →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ₅ ^ 2 * (-φ ξ₅) * Real.exp (w ξ₅ / 2) / Real.sqrt (4 * Real.pi)) ∧
      0.80091 ≤ ξ₅ ^ 2 * (-φ ξ₅) * Real.exp (w ξ₅ / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ₅ ^ 2 * (-φ ξ₅) * Real.exp (w ξ₅ / 2) / Real.sqrt (4 * Real.pi) ≤ 0.800916 ∧
      3556300000 ≤ Real.exp (-w ξ₅) ∧ Real.exp (-w ξ₅) ≤ 3558000000 :=
  Work.Math.BE3Main.main S hS w φ hw hφ0 hφ h0

end Work.Math.BonnorEbertMax3

#print axioms Work.Math.BonnorEbertMax3.bonnor_ebert_third_max
