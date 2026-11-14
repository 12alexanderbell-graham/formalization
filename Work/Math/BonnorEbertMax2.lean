import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Bonnor–Ebert sphere, `BonnorEbertMax2` (FROZEN by run 2026-11-14T1028Z before proof).

Same setting and conventions as `Checked/Math/BonnorEbert.lean`, `BonnorEbertMax.lean` and `BonnorEbertMin.lean`:
the isothermal (Emden–Chandrasekhar) equation w'' + (2/s) w' + e^w = 0 for w = −ψ (ρ = ρ_c e^{−ψ}), w(0) = 0,
φ = w' with one-sided derivatives on [0, S] and φ continuous at 0; the pressure-confined dimensionless mass
m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π); the centre-to-edge density contrast e^{−w(s)}.

The audited headlines `bonnor_ebert_max` and `bonnor_ebert_min` show that the critical sphere ξ₁ carries the
largest mass of every radius and the first minimum ξ₂ ≈ 67 the smallest from ξ₁ on. This file states the next
turn of the spiral: beyond ξ₂ the mass rises to a second maximum at a radius ξ₃ ≈ 734 (density contrast
≈ 2.59 · 10⁵), and that maximum is the strict maximum of the mass over every radius from ξ₂ to S (any S at least
2000). Physically: every pressure-confined isothermal sphere at least as centrally condensed as the first-minimum
sphere has a dimensionless mass between m(ξ₂) ≈ 0.6944 and m(ξ₃) ≈ 0.8307, the upper end attained exactly once.

Windows from floating point (scipy DOP853, rtol 1e-13; unchecked prose): ξ₃ ≈ 733.769, m(ξ₃) ≈ 0.830690,
e^{−w(ξ₃)} ≈ 258577. -/

namespace Work.Math.BonnorEbertMax2
open Set

/-- Bonnor–Ebert sphere, the second maximum of the mass: for every S ≥ 2000 and every solution w of
w'' + (2/s)w' + e^w = 0 on (0, S] with w(0) = 0, w differentiable on [0, S] with derivative φ and φ continuous
at 0, with m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π), there are radii ξ₁ ∈ [6.4507514, 6.4507515],
ξ₂ ∈ [67.0075, 67.0076] and ξ₃ ∈ [733.5, 734] such that m(s) < m(ξ₁) for every other s in [0, S],
m(ξ₂) < m(s) for every other s in [ξ₁, S], m(s) < m(ξ₃) for every other s in [ξ₂, S], m(ξ₃) lies between
0.8306 and 0.8308, and the density contrast e^{−w(ξ₃)} lies between 258300 and 258800. -/
theorem bonnor_ebert_second_max (S : ℝ) (hS : 2000 ≤ S) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    (h0 : w 0 = 0) :
    ∃ ξ₁ ξ₂ ξ₃ : ℝ, 6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧ 67.0075 ≤ ξ₂ ∧ ξ₂ ≤ 67.0076 ∧
      733.5 ≤ ξ₃ ∧ ξ₃ ≤ 734 ∧
      (∀ s ∈ Icc (0 : ℝ) S, s ≠ ξ₁ →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ₁ ^ 2 * (-φ ξ₁) * Real.exp (w ξ₁ / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ s ∈ Icc ξ₁ S, s ≠ ξ₂ →
        ξ₂ ^ 2 * (-φ ξ₂) * Real.exp (w ξ₂ / 2) / Real.sqrt (4 * Real.pi) <
          s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ s ∈ Icc ξ₂ S, s ≠ ξ₃ →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ₃ ^ 2 * (-φ ξ₃) * Real.exp (w ξ₃ / 2) / Real.sqrt (4 * Real.pi)) ∧
      0.8306 ≤ ξ₃ ^ 2 * (-φ ξ₃) * Real.exp (w ξ₃ / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ₃ ^ 2 * (-φ ξ₃) * Real.exp (w ξ₃ / 2) / Real.sqrt (4 * Real.pi) ≤ 0.8308 ∧
      258300 ≤ Real.exp (-w ξ₃) ∧ Real.exp (-w ξ₃) ≤ 258800 := by
  sorry

end Work.Math.BonnorEbertMax2
