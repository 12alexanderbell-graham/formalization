import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Checked.Math.BonnorEbert
import Work.Math.BEEnd
import Work.Math.BETail

/-! Bonnor–Ebert sphere, `BonnorEbertGlobal` (FROZEN by run 2026-11-13T2228Z before proof).

Same setting and conventions as `Checked/Math/BonnorEbert.lean`: the isothermal (Emden–Chandrasekhar)
equation w'' + (2/s) w' + e^w = 0 for w = −ψ (ρ = ρ_c e^{−ψ}), w(0) = 0, φ = w' with one-sided derivatives on
[0, S] and φ continuous at 0; the pressure-confined mass m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π).

The audited headline `bonnor_ebert_critical` shows that m rises strictly up to a radius ξ₁ in a seven-decimal
window and falls strictly from ξ₁ to radius 7. This file states the global companion: on the whole interval
[0, S] (any S at least 7, so on every radius a solution reaches) the first maximum is the strict global maximum
of the mass: every other radius has a strictly smaller mass. Physically, no pressure-confined isothermal
sphere, of any radius, has a larger dimensionless mass than the critical Bonnor–Ebert sphere. -/

namespace Work.Math.BonnorEbertGlobal
open Set

/-- Bonnor–Ebert critical mass is the global maximum: for every S ≥ 7 and every solution w of
w'' + (2/s)w' + e^w = 0 on (0, S] with w(0) = 0, w differentiable on [0, S] with derivative φ and φ continuous
at 0, there is a radius ξ₁ between 6.4507514 and 6.4507515 such that the dimensionless mass
m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π) at every other radius s in [0, S] is strictly smaller than at ξ₁, and the
mass at ξ₁ lies between 1.1822265 and 1.1822266. -/
theorem bonnor_ebert_global (S : ℝ) (hS : 7 ≤ S) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    (h0 : w 0 = 0) :
    ∃ ξ₁ : ℝ, 6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧
      (∀ s ∈ Icc (0 : ℝ) S, s ≠ ξ₁ →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ₁ ^ 2 * (-φ ξ₁) * Real.exp (w ξ₁ / 2) / Real.sqrt (4 * Real.pi)) ∧
      1.1822265 ≤ ξ₁ ^ 2 * (-φ ξ₁) * Real.exp (w ξ₁ / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ₁ ^ 2 * (-φ ξ₁) * Real.exp (w ξ₁ / 2) / Real.sqrt (4 * Real.pi) ≤ 1.1822266 := by
  have hsub : Icc (0 : ℝ) 7 ⊆ Icc 0 S := Icc_subset_Icc le_rfl hS
  have hw7 : ∀ s ∈ Icc (0 : ℝ) 7, HasDerivWithinAt w (φ s) (Icc 0 7) s :=
    fun s hs => (hw s (hsub hs)).mono hsub
  have hφ07 : ContinuousWithinAt φ (Icc 0 7) 0 := hφ0.mono hsub
  have hφ7 : ∀ s ∈ Ioc (0 : ℝ) 7,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 7) s :=
    fun s hs => (hφ s ⟨hs.1, hs.2.trans hS⟩).mono hsub
  obtain ⟨e1, e2, p1, p2⟩ := Work.Math.BEEnd.chain_end hw7 hφ07 hφ7 h0
  have T := Work.Math.BETail.tail S hS w φ hw hφ e1 e2 p1 p2
  obtain ⟨ξ, h1, h2, hmono, hanti, hm1, hm2, -, -⟩ :=
    Checked.Math.BonnorEbert.bonnor_ebert_critical S hS w φ hw hφ0 hφ h0
  refine ⟨ξ, h1, h2, ?_, hm1, hm2⟩
  intro s hs hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hmono ⟨hs.1, hlt.le⟩ ⟨by linarith, le_rfl⟩ hlt
  · rcases le_or_gt s 7 with h7 | h7
    · exact hanti ⟨le_rfl, by linarith⟩ ⟨hgt.le, h7⟩ hgt
    · exact lt_of_lt_of_le (T s ⟨h7.le, hs.2⟩) hm1

end Work.Math.BonnorEbertGlobal

#print axioms Work.Math.BonnorEbertGlobal.bonnor_ebert_global
