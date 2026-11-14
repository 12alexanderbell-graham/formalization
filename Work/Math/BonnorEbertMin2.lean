import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Checked.Math.BEH2Main
import Work.Math.BEOMain

/-! Bonnor–Ebert sphere, `BonnorEbertMin2` (FROZEN by run 2026-11-14T1428Z before proof).

Same setting and conventions as `Checked/Math/BonnorEbert.lean`, `BonnorEbertMax.lean`, `BonnorEbertMin.lean`
and `BonnorEbertMax2.lean`: the isothermal (Emden–Chandrasekhar) equation w'' + (2/s) w' + e^w = 0 for w = −ψ
(ρ = ρ_c e^{−ψ}), w(0) = 0, φ = w' with one-sided derivatives on [0, S] and φ continuous at 0; the
pressure-confined dimensionless mass m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π); the centre-to-edge density contrast
e^{−w(s)}.

The audited headlines `bonnor_ebert_max`, `bonnor_ebert_min` and `bonnor_ebert_second_max` show that the critical
sphere ξ₁ carries the largest mass of every radius, the first minimum ξ₂ ≈ 67 the smallest from ξ₁ on, and the
second maximum ξ₃ ≈ 734 the largest from ξ₂ on. This file states the next turn of the spiral: beyond ξ₃ the mass
falls to a second minimum at a radius ξ₄ ≈ 7850 (density contrast ≈ 3.12 · 10⁷), and that minimum is the strict
minimum of the mass over every radius from ξ₃ to S (any S at least 20000). Physically: every pressure-confined
isothermal sphere at least as centrally condensed as the second-maximum sphere has a dimensionless mass between
m(ξ₄) ≈ 0.787994 and m(ξ₃) ≈ 0.8307, the lower end attained exactly once.

Windows from floating point (scipy, rtol 1e-13; unchecked prose): ξ₄ ≈ 7849.632, m(ξ₄) ≈ 0.7879942,
e^{−w(ξ₄)} ≈ 3.11950 · 10⁷. -/

namespace Work.Math.BonnorEbertMin2
open Set

/-- Bonnor–Ebert sphere, the second minimum of the mass: for every S ≥ 20000 and every solution w of
w'' + (2/s)w' + e^w = 0 on (0, S] with w(0) = 0, w differentiable on [0, S] with derivative φ and φ continuous
at 0, with m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π), there are radii ξ₁ ∈ [6.4507514, 6.4507515],
ξ₂ ∈ [67.0075, 67.0076], ξ₃ ∈ [733.5, 734] and ξ₄ ∈ [7849.5, 7849.75] such that m(s) < m(ξ₁) for every other s
in [0, S], m(ξ₂) < m(s) for every other s in [ξ₁, S], m(s) < m(ξ₃) for every other s in [ξ₂, S],
m(ξ₄) < m(s) for every other s in [ξ₃, S], m(ξ₄) lies between 0.787992 and 0.787995, and the density contrast
e^{−w(ξ₄)} lies between 31193900 and 31196100. -/
theorem bonnor_ebert_second_min (S : ℝ) (hS : 20000 ≤ S) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    (h0 : w 0 = 0) :
    ∃ ξ₁ ξ₂ ξ₃ ξ₄ : ℝ, 6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧ 67.0075 ≤ ξ₂ ∧ ξ₂ ≤ 67.0076 ∧
      733.5 ≤ ξ₃ ∧ ξ₃ ≤ 734 ∧ 7849.5 ≤ ξ₄ ∧ ξ₄ ≤ 7849.75 ∧
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
      0.787992 ≤ ξ₄ ^ 2 * (-φ ξ₄) * Real.exp (w ξ₄ / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ₄ ^ 2 * (-φ ξ₄) * Real.exp (w ξ₄ / 2) / Real.sqrt (4 * Real.pi) ≤ 0.787995 ∧
      31193900 ≤ Real.exp (-w ξ₄) ∧ Real.exp (-w ξ₄) ≤ 31196100 :=
  Work.Math.BEOMain.main S hS w φ hw hφ0 hφ h0

end Work.Math.BonnorEbertMin2
