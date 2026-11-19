import Mathlib
import Work.Math.LE4Chain

/-!
# Mathematics (THE RESULT parts 1 and 5): the constants of the Lane–Emden polytrope of index four

**Question.** The Lane–Emden equation of index four, θ'' + (2/ξ) θ' + θ ^ 4 = 0 with θ(0) = 1
(regular at the singular point ξ = 0), has no closed-form solution. Its first zero ξ₁, the mass
factor −ξ₁ ^ 2 θ'(ξ₁) and the central concentration ξ₁ ^ 3/(3 · mass factor) are entries of the
classical tables of polytropes (Chandrasekhar; Horedt), computed there in floating point. With
indices two and three (`Checked.Math.LaneEmden2`, `Checked.Math.LaneEmden`) this certifies a third
row of those tables with the same validated simulator, generic in the index; the zero lies about
three times further out than for index three, so errors grow over a much longer interval.

**What is stated** (frozen before proof, run 2026-11-19T0428Z): `laneEmden4_constants`, for every
θ, φ satisfying the hypotheses, the bounds on ξ₁, the mass factor and the central concentration
printed in its statement. θ'(0) = 0 is not assumed. Only Mathlib definitions occur in the
statement. Existence of such a θ is a separate theorem (to do).
-/

namespace Work.Math.LaneEmden4
open Set

/-- The program's argument on [0, 15] (helper). -/
theorem core (θ φ : ℝ → ℝ)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) 15, HasDerivWithinAt θ (φ ξ) (Icc 0 15) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 15) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) 15,
      HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ 4) (Icc 0 15) ξ)
    (h0 : θ 0 = 1) :
    ∃ ξ₁ : ℝ, 14.97154634 ≤ ξ₁ ∧ ξ₁ ≤ 14.97154636 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      1.79722991 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 1.79722992 ∧
      622.407879 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 622.407886 := by
  obtain ⟨hneg, hlo, hhi, hom⟩ := Work.Math.LE4Certs.chain hθ hφ0 hφ h0
  have hcont : ContinuousOn θ (Icc 0 15) := fun x hx => (hθ x hx).continuousWithinAt
  have hanti : StrictAntiOn θ (Icc 0 (374288659 / 25000000 : ℝ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 _)
      (hcont.mono (Icc_subset_Icc le_rfl (by norm_num)))
    intro x hx
    rw [interior_Icc] at hx
    have hx7 : x ∈ Ioo (0 : ℝ) 15 := ⟨hx.1, by linarith [hx.2]⟩
    have hd : HasDerivAt θ (φ x) x :=
      (hθ x (Ioo_subset_Icc_self hx7)).hasDerivAt (Icc_mem_nhds hx7.1 hx7.2)
    rw [hd.deriv]
    exact hneg x ⟨hx.1, hx.2.le⟩
  obtain ⟨ξ₁, hξ₁, hz⟩ : ∃ ξ₁ ∈ Icc (748577317 / 50000000 : ℝ) (374288659 / 25000000),
      θ ξ₁ = 0 := by
    have := intermediate_value_Icc' (show (748577317 / 50000000 : ℝ) ≤ 374288659 / 25000000
      by norm_num) (hcont.mono (Icc_subset_Icc (by norm_num) (by norm_num)))
    exact this ⟨hhi.le, hlo.le⟩
  obtain ⟨ho1, ho2⟩ := hom ξ₁ hξ₁
  have ha : (14.97154634 : ℝ) ≤ ξ₁ := by norm_num at hξ₁ ⊢; linarith [hξ₁.1]
  have hb : ξ₁ ≤ (14.97154636 : ℝ) := by norm_num at hξ₁ ⊢; linarith [hξ₁.2]
  have hω1 : (1.79722991 : ℝ) ≤ -(ξ₁ ^ 2 * φ ξ₁) := by norm_num at ho1 ⊢; linarith
  have hω2 : -(ξ₁ ^ 2 * φ ξ₁) ≤ (1.79722992 : ℝ) := by norm_num at ho2 ⊢; linarith
  have hξ0 : 0 ≤ ξ₁ := by linarith
  have hωpos : 0 < 3 * -(ξ₁ ^ 2 * φ ξ₁) := by linarith
  refine ⟨ξ₁, ha, hb, hz, fun ξ hξ => ?_, hω1, hω2, ?_, ?_⟩
  · have hlt := hanti ⟨hξ.1, le_trans hξ.2.le hξ₁.2⟩ ⟨by linarith [hξ₁.1], hξ₁.2⟩ hξ.2
    rw [hz] at hlt
    exact hlt
  · rw [le_div_iff₀ hωpos]
    have h3 : (14.97154634 : ℝ) ^ 3 ≤ ξ₁ ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
    have n : (622.407879 : ℝ) * (3 * 1.79722992) ≤ 14.97154634 ^ 3 := by norm_num
    linarith
  · rw [div_le_iff₀ hωpos]
    have h3 : ξ₁ ^ 3 ≤ (14.97154636 : ℝ) ^ 3 := pow_le_pow_left₀ hξ0 hb 3
    have n : (14.97154636 : ℝ) ^ 3 ≤ 622.407886 * (3 * 1.79722991) := by norm_num
    linarith

/-- Lane–Emden equation of index 4: for every solution θ of θ'' + (2/ξ)θ' + θ⁴ = 0 on (0, 16] with
θ(0) = 1, θ differentiable on [0, 16] with derivative φ, and φ continuous at 0, there is a first
zero ξ₁ of θ with 14.97154634 ≤ ξ₁ ≤ 14.97154636 (θ > 0 before it), at which −ξ₁² θ'(ξ₁) lies
between 1.79722991 and 1.79722992 and ξ₁³/(3 · (−ξ₁² θ'(ξ₁))) lies between 622.407879 and
622.407886. -/
theorem laneEmden4_constants (θ φ : ℝ → ℝ)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) 16, HasDerivWithinAt θ (φ ξ) (Icc 0 16) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 16) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) 16, HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ 4) (Icc 0 16) ξ)
    (h0 : θ 0 = 1) :
    ∃ ξ₁ : ℝ, 14.97154634 ≤ ξ₁ ∧ ξ₁ ≤ 14.97154636 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      1.79722991 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 1.79722992 ∧
      622.407879 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 622.407886 := by
  have hsub : Icc (0 : ℝ) 15 ⊆ Icc 0 16 := Icc_subset_Icc le_rfl (by norm_num)
  exact core θ φ (fun ξ hξ => (hθ ξ (hsub hξ)).mono hsub) (hφ0.mono hsub)
    (fun ξ hξ => (hφ ξ ⟨hξ.1, by linarith [hξ.2]⟩).mono hsub) h0

end Work.Math.LaneEmden4
