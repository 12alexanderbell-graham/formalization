import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Checked.Math.LEChain

/-!
# Mathematics (THE RESULT part 5): the constants of the Lane–Emden polytrope of index three

**Question.** The Lane–Emden equation of index three, θ'' + (2/ξ) θ' + θ³ = 0 with θ(0) = 1
(regular at the singular point ξ = 0), has no closed-form solution. Its first zero ξ₁ and the number
ω₃ = −ξ₁² θ'(ξ₁) are classical constants: ω₃ is the numerical factor of the Chandrasekhar mass,
ξ₁ fixes the radius of Eddington's standard model, and ξ₁³/(3ω₃) is its central concentration.
Every value in the literature found by the screen of run 2026-11-05T0028Z (Chandrasekhar 1939;
Horedt 1986 tables; Boyd 2011) comes from floating-point computation; the screen and the referee
found no rigorous enclosure.

**What is stated** (frozen before proof in `Work/Math/LaneEmden.lean`, commit 5a06f66; statement
promoted byte-identical): `laneEmden3_constants`, for every θ, φ satisfying the hypotheses, the
bounds on ξ₁, ω₃ and ξ₁³/(3ω₃) printed in its statement. θ'(0) = 0 is not assumed: it follows.
Existence of such a θ: `Checked.Math.LEExists.exists_solution` (non-vacuity witness in
`Checked/Trust/Witnesses.lean`). Only Mathlib definitions occur in the statement.
-/

namespace Checked.Math.LaneEmden
open Set

/-- The program's argument on [0, 69/10] (helper; the headline below and the closed blind
restatement both use it). -/
theorem core (θ φ : ℝ → ℝ)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) (69 / 10), HasDerivWithinAt θ (φ ξ) (Icc 0 (69 / 10)) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 (69 / 10)) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) (69 / 10),
      HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ 3) (Icc 0 (69 / 10)) ξ)
    (h0 : θ 0 = 1) :
    ∃ ξ₁ : ℝ, 6.896848615 ≤ ξ₁ ∧ ξ₁ ≤ 6.896848625 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      2.018235945 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 2.018235955 ∧
      54.1824805 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 54.1824815 := by
  obtain ⟨hneg, hlo, hhi, hom⟩ := Checked.Math.LECerts.chain hθ hφ0 hφ h0
  have hcont : ContinuousOn θ (Icc 0 (69 / 10)) := fun x hx => (hθ x hx).continuousWithinAt
  have hanti : StrictAntiOn θ (Icc 0 (55174789 / 8000000 : ℝ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 _)
      (hcont.mono (Icc_subset_Icc le_rfl (by norm_num)))
    intro x hx
    rw [interior_Icc] at hx
    have hx7 : x ∈ Ioo (0 : ℝ) (69 / 10) := ⟨hx.1, by linarith [hx.2]⟩
    have hd : HasDerivAt θ (φ x) x :=
      (hθ x (Ioo_subset_Icc_self hx7)).hasDerivAt (Icc_mem_nhds hx7.1 hx7.2)
    rw [hd.deriv]
    exact hneg x ⟨hx.1, hx.2.le⟩
  obtain ⟨ξ₁, hξ₁, hz⟩ : ∃ ξ₁ ∈ Icc (1379369723 / 200000000 : ℝ) (55174789 / 8000000),
      θ ξ₁ = 0 := by
    have := intermediate_value_Icc' (show (1379369723 / 200000000 : ℝ) ≤ 55174789 / 8000000
      by norm_num) (hcont.mono (Icc_subset_Icc (by norm_num) (by norm_num)))
    exact this ⟨hhi.le, hlo.le⟩
  obtain ⟨ho1, ho2⟩ := hom ξ₁ hξ₁
  have ha : (6.896848615 : ℝ) ≤ ξ₁ := by norm_num at hξ₁ ⊢; linarith [hξ₁.1]
  have hb : ξ₁ ≤ (6.896848625 : ℝ) := by norm_num at hξ₁ ⊢; linarith [hξ₁.2]
  have hω1 : (2.018235945 : ℝ) ≤ -(ξ₁ ^ 2 * φ ξ₁) := by norm_num at ho1 ⊢; linarith
  have hω2 : -(ξ₁ ^ 2 * φ ξ₁) ≤ (2.018235955 : ℝ) := by norm_num at ho2 ⊢; linarith
  have hξ0 : 0 ≤ ξ₁ := by linarith
  have hωpos : 0 < 3 * -(ξ₁ ^ 2 * φ ξ₁) := by linarith
  refine ⟨ξ₁, ha, hb, hz, fun ξ hξ => ?_, hω1, hω2, ?_, ?_⟩
  · have hlt := hanti ⟨hξ.1, le_trans hξ.2.le hξ₁.2⟩ ⟨by linarith [hξ₁.1], hξ₁.2⟩ hξ.2
    rw [hz] at hlt
    exact hlt
  · rw [le_div_iff₀ hωpos]
    have h3 : (6.896848615 : ℝ) ^ 3 ≤ ξ₁ ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
    have n : (54.1824805 : ℝ) * (3 * 2.018235955) ≤ 6.896848615 ^ 3 := by norm_num
    linarith
  · rw [div_le_iff₀ hωpos]
    have h3 : ξ₁ ^ 3 ≤ (6.896848625 : ℝ) ^ 3 := pow_le_pow_left₀ hξ0 hb 3
    have n : (6.896848625 : ℝ) ^ 3 ≤ 54.1824815 * (3 * 2.018235945) := by norm_num
    linarith

/-- Lane–Emden equation of index 3: for every solution θ of θ'' + (2/ξ)θ' + θ³ = 0 on (0, 7] with
θ(0) = 1, θ differentiable on [0, 7] with derivative φ, and φ continuous at 0, there is a first zero
ξ₁ of θ with 6.896848615 ≤ ξ₁ ≤ 6.896848625 (θ > 0 before it), at which the Chandrasekhar-mass
constant −ξ₁² θ'(ξ₁) lies between 2.018235945 and 2.018235955 and ξ₁³/(3 · (−ξ₁² θ'(ξ₁))) lies
between 54.1824805 and 54.1824815. -/
theorem laneEmden3_constants (θ φ : ℝ → ℝ)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) 7, HasDerivWithinAt θ (φ ξ) (Icc 0 7) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 7) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) 7, HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ 3) (Icc 0 7) ξ)
    (h0 : θ 0 = 1) :
    ∃ ξ₁ : ℝ, 6.896848615 ≤ ξ₁ ∧ ξ₁ ≤ 6.896848625 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      2.018235945 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 2.018235955 ∧
      54.1824805 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 54.1824815 := by
  have hsub : Icc (0 : ℝ) (69 / 10) ⊆ Icc 0 7 := Icc_subset_Icc le_rfl (by norm_num)
  exact core θ φ (fun ξ hξ => (hθ ξ (hsub hξ)).mono hsub) (hφ0.mono hsub)
    (fun ξ hξ => (hφ ξ ⟨hξ.1, by linarith [hξ.2]⟩).mono hsub) h0

end Checked.Math.LaneEmden
