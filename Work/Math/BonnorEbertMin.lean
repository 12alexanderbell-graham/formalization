import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Work.Math.BEHMain

/-! Bonnor–Ebert sphere, `BonnorEbertMin` (FROZEN by run 2026-11-14T0428Z before proof).

Same setting and conventions as `Checked/Math/BonnorEbert.lean` and `Checked/Math/BonnorEbertMax.lean`: the
isothermal (Emden–Chandrasekhar) equation w'' + (2/s) w' + e^w = 0 for w = −ψ (ρ = ρ_c e^{−ψ}), w(0) = 0,
φ = w' with one-sided derivatives on [0, S] and φ continuous at 0; the pressure-confined dimensionless mass
m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π); the centre-to-edge density contrast e^{−w(s)}.

The audited headline `bonnor_ebert_max` shows that the first maximum ξ₁ (the critical Bonnor–Ebert sphere) is
the strict maximum of the mass over every radius. This file states the other end of the range of the
supercritical branch: beyond ξ₁ the mass falls to a first minimum at a radius ξ₂ ≈ 67 (density contrast
≈ 2580), and that minimum is the strict minimum of the mass over every radius from ξ₁ to S (any S at least
150). Physically: every pressure-confined isothermal sphere at least as centrally condensed as the critical one
has a dimensionless mass between m(ξ₂) ≈ 0.6944 and m(ξ₁) ≈ 1.1822, and both ends are attained exactly once.

Windows from floating point (scipy DOP853, rtol 2e-14; unchecked prose): ξ₂ ≈ 67.0075487, m(ξ₂) ≈ 0.6943665211,
e^{−w(ξ₂)} ≈ 2579.69733. -/

namespace Work.Math.BonnorEbertMin
open Set

/-- Bonnor–Ebert sphere, the first minimum of the mass: for every S ≥ 150 and every solution w of
w'' + (2/s)w' + e^w = 0 on (0, S] with w(0) = 0, w differentiable on [0, S] with derivative φ and φ continuous
at 0, with m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π), there are radii ξ₁ ∈ [6.4507514, 6.4507515] and
ξ₂ ∈ [67.0075, 67.0076] such that m(s) < m(ξ₁) for every other s in [0, S], m(ξ₂) < m(s) for every other s in
[ξ₁, S], m(ξ₂) lies between 0.694366 and 0.694367, and the density contrast e^{−w(ξ₂)} lies between 2579.69 and
2579.71. -/
theorem bonnor_ebert_min (S : ℝ) (hS : 150 ≤ S) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    (h0 : w 0 = 0) :
    ∃ ξ₁ ξ₂ : ℝ, 6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧ 67.0075 ≤ ξ₂ ∧ ξ₂ ≤ 67.0076 ∧
      (∀ s ∈ Icc (0 : ℝ) S, s ≠ ξ₁ →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ₁ ^ 2 * (-φ ξ₁) * Real.exp (w ξ₁ / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ s ∈ Icc ξ₁ S, s ≠ ξ₂ →
        ξ₂ ^ 2 * (-φ ξ₂) * Real.exp (w ξ₂ / 2) / Real.sqrt (4 * Real.pi) <
          s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) ∧
      0.694366 ≤ ξ₂ ^ 2 * (-φ ξ₂) * Real.exp (w ξ₂ / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ₂ ^ 2 * (-φ ξ₂) * Real.exp (w ξ₂ / 2) / Real.sqrt (4 * Real.pi) ≤ 0.694367 ∧
      2579.69 ≤ Real.exp (-w ξ₂) ∧ Real.exp (-w ξ₂) ≤ 2579.71 :=
  Work.Math.BEHMain.main S hS w φ hw hφ0 hφ h0

end Work.Math.BonnorEbertMin
