import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Checked.Math.BonnorEbert
import Checked.Math.BEEnd
import Checked.Math.BETail

/-! Bonnor–Ebert sphere, `BonnorEbertMax`: the critical state of the pressure-confined isothermal sphere is the strict maximum of the dimensionless mass over every radius the solution reaches. Promoted from `Work/Math/BonnorEbertGlobal.lean` (frozen and proved by run 2026-11-13T2228Z); the route is `BEEnd` (state at the end radius of the certified cells) and `BETail` (Volterra's function beyond it). -/

namespace Checked.Math.BonnorEbertMax
open Set

/-- Bonnor–Ebert critical sphere, max of the mass: for every S ≥ 7 and every solution w of
w'' + (2/s)w' + e^w = 0 on (0, S] with w(0) = 0, w differentiable on [0, S] with derivative φ and φ continuous
at 0, there is a radius ξ₁ between 6.4507514 and 6.4507515 such that the dimensionless mass
m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π) has m(s) < m(ξ₁) for s in [0, S] with s ≠ ξ₁;
and m(ξ₁) lies between 1.1822265 and 1.1822266. -/
theorem bonnor_ebert_max (S : ℝ) (hS : 7 ≤ S) (w φ : ℝ → ℝ)
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
  obtain ⟨e1, e2, p1, p2⟩ := Checked.Math.BEEnd.chain_end hw7 hφ07 hφ7 h0
  have T := Checked.Math.BETail.tail S hS w φ hw hφ e1 e2 p1 p2
  obtain ⟨ξ, h1, h2, hmono, hanti, hm1, hm2, -, -⟩ :=
    Checked.Math.BonnorEbert.bonnor_ebert_critical S hS w φ hw hφ0 hφ h0
  refine ⟨ξ, h1, h2, ?_, hm1, hm2⟩
  intro s hs hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hmono ⟨hs.1, hlt.le⟩ ⟨by linarith, le_rfl⟩ hlt
  · rcases le_or_gt s 7 with h7 | h7
    · exact hanti ⟨le_rfl, by linarith⟩ ⟨hgt.le, h7⟩ hgt
    · exact lt_of_lt_of_le (T s ⟨h7.le, hs.2⟩) hm1

end Checked.Math.BonnorEbertMax
