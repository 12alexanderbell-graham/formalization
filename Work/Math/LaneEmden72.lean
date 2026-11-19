import Mathlib
import Work.Math.LE72Chain

/-!
# Mathematics (THE RESULT parts 1 and 5): the constants of the Lane–Emden polytrope of index seven halves

**Question.** The Lane–Emden equation of index seven halves, θ'' + (2/ξ) θ' + θ ^ (7/2) = 0 with
θ(0) = 1 (regular at the singular point ξ = 0), is a row of the classical tables of polytropes
(Chandrasekhar; Horedt), computed there in floating point. It has no closed-form solution. Its
first zero ξ₁, the mass factor −ξ₁ ^ 2 θ'(ξ₁) and the central concentration ξ₁ ^ 3/(3 · mass
factor) are the entries of that row. Indices two, three, four, three halves and five halves are certified
(`Checked.Math.LaneEmden2`, `Checked.Math.LaneEmden`, `Checked.Math.LaneEmden4`,
`Checked.Math.LaneEmden32`, `Checked.Math.LaneEmden52`); θ ^ (7/2) has no polynomial Taylor recursion
and is not smooth at the zero of θ (its fourth derivative in θ is unbounded there).

**What is stated** (frozen before proof, run 2026-11-19T2228Z): `laneEmden72_constants`, for every
θ, φ satisfying the hypotheses, the bounds on ξ₁, the mass factor and the central concentration
printed in its statement. θ'(0) = 0 is not assumed. The power is Mathlib's real power `Real.rpow`;
for a negative base it returns zero at this exponent, so past the zero of θ the hypothesis reads
θ'' + (2/ξ) θ' = 0; the conclusions concern [0, ξ₁], where θ is not negative. Only Mathlib
definitions occur in the statement. Existence of such a θ:
`Work.Math.LE72Exists.exists_solution` (checked in a separate module).
-/

namespace Work.Math.LaneEmden72
open Set

/-- The program's argument on [0, 477/50] (helper). -/
theorem core (θ φ : ℝ → ℝ)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) (477 / 50), HasDerivWithinAt θ (φ ξ) (Icc 0 (477 / 50)) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 (477 / 50)) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) (477 / 50),
      HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ ((7 : ℝ) / 2)) (Icc 0 (477 / 50)) ξ)
    (h0 : θ 0 = 1) :
    ∃ ξ₁ : ℝ, 9.53580534 ≤ ξ₁ ∧ ξ₁ ≤ 9.53580535 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      1.89055709 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 1.89055710 ∧
      152.8836627 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 152.8836632 := by
  have hφg : ∀ ξ ∈ Ioc (0 : ℝ) (477 / 50),
      HasDerivWithinAt φ (-(2 / ξ * φ ξ) - Work.Math.LE72Cell.g72 (θ ξ)) (Icc 0 (477 / 50)) ξ :=
    fun ξ hξ => by rw [← Work.Math.LE72Cell.rpow72_eq]; exact hφ ξ hξ
  obtain ⟨hneg, hlo, hhi, hom⟩ := Work.Math.LE72Certs.chain hθ hφ0 hφg h0
  have hcont : ContinuousOn θ (Icc 0 (477 / 50)) := fun x hx => (hθ x hx).continuousWithinAt
  have hanti : StrictAntiOn θ (Icc 0 (1907161069 / 200000000 : ℝ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 _)
      (hcont.mono (Icc_subset_Icc le_rfl (by norm_num)))
    intro x hx
    rw [interior_Icc] at hx
    have hx4 : x ∈ Ioo (0 : ℝ) (477 / 50) := ⟨hx.1, by linarith [hx.2]⟩
    have hd : HasDerivAt θ (φ x) x :=
      (hθ x (Ioo_subset_Icc_self hx4)).hasDerivAt (Icc_mem_nhds hx4.1 hx4.2)
    rw [hd.deriv]
    exact hneg x ⟨hx.1, hx.2.le⟩
  obtain ⟨ξ₁, hξ₁, hz⟩ : ∃ ξ₁ ∈ Icc (9535805343 / 1000000000 : ℝ) (1907161069 / 200000000),
      θ ξ₁ = 0 := by
    have := intermediate_value_Icc' (show (9535805343 / 1000000000 : ℝ) ≤ 1907161069 / 200000000
      by norm_num) (hcont.mono (Icc_subset_Icc (by norm_num) (by norm_num)))
    exact this ⟨hhi.le, hlo.le⟩
  obtain ⟨ho1, ho2⟩ := hom ξ₁ hξ₁
  have ha : (9.53580534 : ℝ) ≤ ξ₁ := by norm_num at hξ₁ ⊢; linarith [hξ₁.1]
  have hb : ξ₁ ≤ (9.53580535 : ℝ) := by norm_num at hξ₁ ⊢; linarith [hξ₁.2]
  have ha' : (9535805343 / 1000000000 : ℝ) ≤ ξ₁ := hξ₁.1
  have hb' : ξ₁ ≤ (1907161069 / 200000000 : ℝ) := hξ₁.2
  have hω1 : (1.89055709 : ℝ) ≤ -(ξ₁ ^ 2 * φ ξ₁) := by norm_num at ho1 ⊢; linarith
  have hω2 : -(ξ₁ ^ 2 * φ ξ₁) ≤ (1.89055710 : ℝ) := by norm_num at ho2 ⊢; linarith
  have hξ0 : 0 ≤ ξ₁ := by linarith
  have hωpos : 0 < 3 * -(ξ₁ ^ 2 * φ ξ₁) := by linarith
  refine ⟨ξ₁, ha, hb, hz, fun ξ hξ => ?_, hω1, hω2, ?_, ?_⟩
  · have hlt := hanti ⟨hξ.1, le_trans hξ.2.le hξ₁.2⟩ ⟨by linarith [hξ₁.1], hξ₁.2⟩ hξ.2
    rw [hz] at hlt
    exact hlt
  · rw [le_div_iff₀ hωpos]
    have h3 : (9535805343 / 1000000000 : ℝ) ^ 3 ≤ ξ₁ ^ 3 := pow_le_pow_left₀ (by norm_num) ha' 3
    have n : (152.8836627 : ℝ) * (3 * (1890557095 / 1000000000)) ≤ (9535805343 / 1000000000) ^ 3 := by
      norm_num
    norm_num at ho2
    nlinarith
  · rw [div_le_iff₀ hωpos]
    have h3 : ξ₁ ^ 3 ≤ (1907161069 / 200000000 : ℝ) ^ 3 := pow_le_pow_left₀ hξ0 hb' 3
    have n : (1907161069 / 200000000 : ℝ) ^ 3 ≤ 152.8836632 * (3 * (472639273 / 250000000)) := by
      norm_num
    norm_num at ho1
    nlinarith

/-- Lane–Emden equation θ'' + (2/ξ)θ' + θ ^ (7/2) = 0: for every solution θ on (0, 10] with
θ(0) = 1, θ differentiable on [0, 10] with derivative φ, and φ continuous at 0, there is a zero ξ₁ of
θ with 9.53580534 ≤ ξ₁ ≤ 9.53580535 and θ > 0 on [0, ξ₁), at which −ξ₁² θ'(ξ₁) lies between
1.89055709 and 1.89055710 and ξ₁³/(3 · (−ξ₁² θ'(ξ₁))) lies between 152.8836627 and 152.8836632. -/
theorem laneEmden72_constants (θ φ : ℝ → ℝ)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) 10, HasDerivWithinAt θ (φ ξ) (Icc 0 10) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 10) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) 10,
      HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ ((7 : ℝ) / 2)) (Icc 0 10) ξ)
    (h0 : θ 0 = 1) :
    ∃ ξ₁ : ℝ, 9.53580534 ≤ ξ₁ ∧ ξ₁ ≤ 9.53580535 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      1.89055709 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 1.89055710 ∧
      152.8836627 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 152.8836632 := by
  have hsub : Icc (0 : ℝ) (477 / 50) ⊆ Icc 0 10 := Icc_subset_Icc le_rfl (by norm_num)
  exact core θ φ (fun ξ hξ => (hθ ξ (hsub hξ)).mono hsub) (hφ0.mono hsub)
    (fun ξ hξ => (hφ ξ ⟨hξ.1, by linarith [hξ.2]⟩).mono hsub) h0

end Work.Math.LaneEmden72
