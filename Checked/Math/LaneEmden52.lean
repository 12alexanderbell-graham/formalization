import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Checked.Math.LE52Chain

/-!
# Mathematics (THE RESULT parts 1 and 5): the constants of the Lane–Emden polytrope of index five halves

**Question.** The Lane–Emden equation of index five halves, θ'' + (2/ξ) θ' + θ ^ (5/2) = 0 with
θ(0) = 1 (regular at the singular point ξ = 0), is a row of the classical tables of polytropes
(Chandrasekhar; Horedt), computed there in floating point. It has no closed-form solution. Its
first zero ξ₁, the mass factor −ξ₁ ^ 2 θ'(ξ₁) and the central concentration ξ₁ ^ 3/(3 · mass
factor) are the entries of that row. Indices two, three, four and three halves are certified
(`Checked.Math.LaneEmden2`, `Checked.Math.LaneEmden`, `Checked.Math.LaneEmden4`,
`Checked.Math.LaneEmden32`); θ ^ (5/2) has no polynomial Taylor recursion and is not smooth at the
zero of θ (its third derivative in θ is unbounded there).

**What is stated** (frozen before proof in `Work/Math/LaneEmden52.lean`, statement promoted
byte-identical): `laneEmden52_constants`, for every
θ, φ satisfying the hypotheses, the bounds on ξ₁, the mass factor and the central concentration
printed in its statement. θ'(0) = 0 is not assumed. The power is Mathlib's real power `Real.rpow`;
for a negative base it returns zero at this exponent, so past the zero of θ the hypothesis reads
θ'' + (2/ξ) θ' = 0; the conclusions concern [0, ξ₁], where θ is not negative. Only Mathlib
definitions occur in the statement. Existence of such a θ:
`Checked.Math.LE52Exists.exists_solution` (non-vacuity witness in `Checked/Trust/Witnesses.lean`).
-/

namespace Checked.Math.LaneEmden52
open Set

/-- The program's argument on [0, 134/25] (helper). -/
theorem core (θ φ : ℝ → ℝ)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) (134 / 25), HasDerivWithinAt θ (φ ξ) (Icc 0 (134 / 25)) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 (134 / 25)) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) (134 / 25),
      HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ ((5 : ℝ) / 2)) (Icc 0 (134 / 25)) ξ)
    (h0 : θ 0 = 1) :
    ∃ ξ₁ : ℝ, 5.35527545 ≤ ξ₁ ∧ ξ₁ ≤ 5.35527546 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      2.18719956 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 2.18719957 ∧
      23.40646222 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 23.40646231 := by
  have hφg : ∀ ξ ∈ Ioc (0 : ℝ) (134 / 25),
      HasDerivWithinAt φ (-(2 / ξ * φ ξ) - Checked.Math.LE52Cell.g52 (θ ξ)) (Icc 0 (134 / 25)) ξ :=
    fun ξ hξ => by rw [← Checked.Math.LE52Cell.rpow52_eq]; exact hφ ξ hξ
  obtain ⟨hneg, hlo, hhi, hom⟩ := Checked.Math.LE52Certs.chain hθ hφ0 hφg h0
  have hcont : ContinuousOn θ (Icc 0 (134 / 25)) := fun x hx => (hθ x hx).continuousWithinAt
  have hanti : StrictAntiOn θ (Icc 0 (267763773 / 50000000 : ℝ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 _)
      (hcont.mono (Icc_subset_Icc le_rfl (by norm_num)))
    intro x hx
    rw [interior_Icc] at hx
    have hx4 : x ∈ Ioo (0 : ℝ) (134 / 25) := ⟨hx.1, by linarith [hx.2]⟩
    have hd : HasDerivAt θ (φ x) x :=
      (hθ x (Ioo_subset_Icc_self hx4)).hasDerivAt (Icc_mem_nhds hx4.1 hx4.2)
    rw [hd.deriv]
    exact hneg x ⟨hx.1, hx.2.le⟩
  obtain ⟨ξ₁, hξ₁, hz⟩ : ∃ ξ₁ ∈ Icc (2677637729 / 500000000 : ℝ) (267763773 / 50000000),
      θ ξ₁ = 0 := by
    have := intermediate_value_Icc' (show (2677637729 / 500000000 : ℝ) ≤ 267763773 / 50000000
      by norm_num) (hcont.mono (Icc_subset_Icc (by norm_num) (by norm_num)))
    exact this ⟨hhi.le, hlo.le⟩
  obtain ⟨ho1, ho2⟩ := hom ξ₁ hξ₁
  have ha : (5.35527545 : ℝ) ≤ ξ₁ := by norm_num at hξ₁ ⊢; linarith [hξ₁.1]
  have hb : ξ₁ ≤ (5.35527546 : ℝ) := by norm_num at hξ₁ ⊢; linarith [hξ₁.2]
  have ha' : (2677637729 / 500000000 : ℝ) ≤ ξ₁ := hξ₁.1
  have hb' : ξ₁ ≤ (267763773 / 50000000 : ℝ) := hξ₁.2
  have hω1 : (2.18719956 : ℝ) ≤ -(ξ₁ ^ 2 * φ ξ₁) := by norm_num at ho1 ⊢; linarith
  have hω2 : -(ξ₁ ^ 2 * φ ξ₁) ≤ (2.18719957 : ℝ) := by norm_num at ho2 ⊢; linarith
  have hξ0 : 0 ≤ ξ₁ := by linarith
  have hωpos : 0 < 3 * -(ξ₁ ^ 2 * φ ξ₁) := by linarith
  refine ⟨ξ₁, ha, hb, hz, fun ξ hξ => ?_, hω1, hω2, ?_, ?_⟩
  · have hlt := hanti ⟨hξ.1, le_trans hξ.2.le hξ₁.2⟩ ⟨by linarith [hξ₁.1], hξ₁.2⟩ hξ.2
    rw [hz] at hlt
    exact hlt
  · rw [le_div_iff₀ hωpos]
    have h3 : (2677637729 / 500000000 : ℝ) ^ 3 ≤ ξ₁ ^ 3 := pow_le_pow_left₀ (by norm_num) ha' 3
    have n : (23.40646222 : ℝ) * (3 * (2187199567 / 1000000000)) ≤ (2677637729 / 500000000) ^ 3 := by
      norm_num
    norm_num at ho2
    nlinarith
  · rw [div_le_iff₀ hωpos]
    have h3 : ξ₁ ^ 3 ≤ (267763773 / 50000000 : ℝ) ^ 3 := pow_le_pow_left₀ hξ0 hb' 3
    have n : (267763773 / 50000000 : ℝ) ^ 3 ≤ 23.40646231 * (3 * (546799891 / 250000000)) := by
      norm_num
    norm_num at ho1
    nlinarith

/-- Lane–Emden equation θ'' + (2/ξ)θ' + θ ^ (5/2) = 0: for every solution θ on (0, 6] with
θ(0) = 1, θ differentiable on [0, 6] with derivative φ, and φ continuous at 0, there is a zero ξ₁ of
θ with 5.35527545 ≤ ξ₁ ≤ 5.35527546 and θ > 0 on [0, ξ₁), at which −ξ₁² θ'(ξ₁) lies between
2.18719956 and 2.18719957 and ξ₁³/(3 · (−ξ₁² θ'(ξ₁))) lies between 23.40646222 and 23.40646231. -/
theorem laneEmden52_constants (θ φ : ℝ → ℝ)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) 6, HasDerivWithinAt θ (φ ξ) (Icc 0 6) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 6) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) 6,
      HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ ((5 : ℝ) / 2)) (Icc 0 6) ξ)
    (h0 : θ 0 = 1) :
    ∃ ξ₁ : ℝ, 5.35527545 ≤ ξ₁ ∧ ξ₁ ≤ 5.35527546 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      2.18719956 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 2.18719957 ∧
      23.40646222 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 23.40646231 := by
  have hsub : Icc (0 : ℝ) (134 / 25) ⊆ Icc 0 6 := Icc_subset_Icc le_rfl (by norm_num)
  exact core θ φ (fun ξ hξ => (hθ ξ (hsub hξ)).mono hsub) (hφ0.mono hsub)
    (fun ξ hξ => (hφ ξ ⟨hξ.1, by linarith [hξ.2]⟩).mono hsub) h0

end Checked.Math.LaneEmden52
