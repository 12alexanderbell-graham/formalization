import Mathlib
import Work.Math.BEMain

/-! Bonnor–Ebert sphere, `BonnorEbert` (FROZEN by run 2026-11-12T0427Z in auditor role; to move to
`Work/Math/BonnorEbert.lean` byte-identical once the LOCK is free).

The isothermal (Emden–Chandrasekhar) equation in the variable w = −ψ, where ρ = ρ_c e^{−ψ} is the density
of a self-gravitating isothermal gas sphere and ξ the dimensionless radius: w'' + (2/ξ) w' + e^w = 0 with
w(0) = 0 and w'(0) = 0 (regular centre). A sphere truncated at radius ξ and confined by external pressure
has dimensionless mass m(ξ) = ξ² (−w'(ξ)) e^{w(ξ)/2} / √(4π) (Bonnor 1956, Ebert 1955: M = m c_s⁴ G^{−3/2} P_ext^{−1/2}),
and centre-to-edge density contrast ρ_c/ρ(ξ) = e^{−w(ξ)}. The Bonnor–Ebert critical state is the first
maximum of m. Conventions: φ is the derivative of w, one-sided derivatives on [0, S], and φ is only required
to be continuous at 0 (no condition φ(0) = 0 is assumed: the equation forces it). -/

namespace Work.Math.BonnorEbert
open Set

/-- Bonnor–Ebert critical sphere: for every S ≥ 7 and every solution w of w'' + (2/s)w' + e^w = 0 on
(0, S] with w(0) = 0, w differentiable on [0, S] with derivative φ and φ continuous at 0, the dimensionless
mass m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π) increases strictly on [0, ξ₁] and decreases strictly on [ξ₁, 7] for a
radius ξ₁ between 6.4507514 and 6.4507515; there the mass lies between 1.1822265 and 1.1822266 and the
centre-to-edge density contrast e^{−w(ξ₁)} between 14.042032 and 14.042033. -/
theorem bonnor_ebert_critical (S : ℝ) (hS : 7 ≤ S) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    (h0 : w 0 = 0) :
    ∃ ξ₁ : ℝ, 6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧
      StrictMonoOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi))
        (Icc 0 ξ₁) ∧
      StrictAntiOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi))
        (Icc ξ₁ 7) ∧
      1.1822265 ≤ ξ₁ ^ 2 * (-φ ξ₁) * Real.exp (w ξ₁ / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ₁ ^ 2 * (-φ ξ₁) * Real.exp (w ξ₁ / 2) / Real.sqrt (4 * Real.pi) ≤ 1.1822266 ∧
      14.042032 ≤ Real.exp (-w ξ₁) ∧ Real.exp (-w ξ₁) ≤ 14.042033 :=
  Work.Math.BEMain.bonnor_ebert_critical S hS w φ hw hφ0 hφ h0

end Work.Math.BonnorEbert
