import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Checked.Math.LE2Chain

/-!
# Mathematics (THE RESULT parts 1 and 5): the constants of the Lane–Emden polytrope of index two

**Question.** The Lane–Emden equation of index two, θ'' + (2/ξ) θ' + θ ^ 2 = 0 with θ(0) = 1
(regular at the singular point ξ = 0), has no closed-form solution. Its first zero ξ₁, the mass
factor −ξ₁ ^ 2 θ'(ξ₁) and the central concentration ξ₁ ^ 3/(3 · mass factor) are entries of the
classical tables of polytropes (Chandrasekhar; Horedt), computed there in floating point. With
index three (`Checked.Math.LaneEmden`) this certifies a second row of those tables, with the
validated simulator now generic in the index (`Checked.Math.LENCellQ`).

**What is stated** (frozen before proof in `Work/Math/LaneEmden2.lean`, statement promoted
byte-identical): `laneEmden2_constants`, for every θ, φ satisfying the hypotheses, the bounds on ξ₁,
the mass factor and the central concentration printed in its statement. θ'(0) = 0 is not assumed.
Only Mathlib definitions occur in the statement. Existence of such a θ:
`Checked.Math.LE2Exists.exists_solution` (non-vacuity witness in `Checked/Trust/Witnesses.lean`).
-/

namespace Checked.Math.LaneEmden2
open Set

/-- The program's argument on [0, 9/2] (helper). -/
theorem core (θ φ : ℝ → ℝ)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) (9 / 2), HasDerivWithinAt θ (φ ξ) (Icc 0 (9 / 2)) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 (9 / 2)) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) (9 / 2),
      HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ 2) (Icc 0 (9 / 2)) ξ)
    (h0 : θ 0 = 1) :
    ∃ ξ₁ : ℝ, 4.3528745959 ≤ ξ₁ ∧ ξ₁ ≤ 4.3528745960 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      2.4110460120 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 2.4110460122 ∧
      11.402542860 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 11.402542864 := by
  obtain ⟨hneg, hlo, hhi, hom⟩ := Checked.Math.LE2Certs.chain hθ hφ0 hφ h0
  have hcont : ContinuousOn θ (Icc 0 (9 / 2)) := fun x hx => (hθ x hx).continuousWithinAt
  have hanti : StrictAntiOn θ (Icc 0 (1088218649 / 250000000 : ℝ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 _)
      (hcont.mono (Icc_subset_Icc le_rfl (by norm_num)))
    intro x hx
    rw [interior_Icc] at hx
    have hx7 : x ∈ Ioo (0 : ℝ) (9 / 2) := ⟨hx.1, by linarith [hx.2]⟩
    have hd : HasDerivAt θ (φ x) x :=
      (hθ x (Ioo_subset_Icc_self hx7)).hasDerivAt (Icc_mem_nhds hx7.1 hx7.2)
    rw [hd.deriv]
    exact hneg x ⟨hx.1, hx.2.le⟩
  obtain ⟨ξ₁, hξ₁, hz⟩ : ∃ ξ₁ ∈ Icc (43528745959 / 10000000000 : ℝ) (1088218649 / 250000000),
      θ ξ₁ = 0 := by
    have := intermediate_value_Icc' (show (43528745959 / 10000000000 : ℝ) ≤ 1088218649 / 250000000
      by norm_num) (hcont.mono (Icc_subset_Icc (by norm_num) (by norm_num)))
    exact this ⟨hhi.le, hlo.le⟩
  obtain ⟨ho1, ho2⟩ := hom ξ₁ hξ₁
  have ha : (4.3528745959 : ℝ) ≤ ξ₁ := by norm_num at hξ₁ ⊢; linarith [hξ₁.1]
  have hb : ξ₁ ≤ (4.3528745960 : ℝ) := by norm_num at hξ₁ ⊢; linarith [hξ₁.2]
  have hω1 : (2.4110460120 : ℝ) ≤ -(ξ₁ ^ 2 * φ ξ₁) := by norm_num at ho1 ⊢; linarith
  have hω2 : -(ξ₁ ^ 2 * φ ξ₁) ≤ (2.4110460122 : ℝ) := by norm_num at ho2 ⊢; linarith
  have hξ0 : 0 ≤ ξ₁ := by linarith
  have hωpos : 0 < 3 * -(ξ₁ ^ 2 * φ ξ₁) := by linarith
  refine ⟨ξ₁, ha, hb, hz, fun ξ hξ => ?_, hω1, hω2, ?_, ?_⟩
  · have hlt := hanti ⟨hξ.1, le_trans hξ.2.le hξ₁.2⟩ ⟨by linarith [hξ₁.1], hξ₁.2⟩ hξ.2
    rw [hz] at hlt
    exact hlt
  · rw [le_div_iff₀ hωpos]
    have h3 : (4.3528745959 : ℝ) ^ 3 ≤ ξ₁ ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
    have n : (11.402542860 : ℝ) * (3 * 2.4110460122) ≤ 4.3528745959 ^ 3 := by norm_num
    linarith
  · rw [div_le_iff₀ hωpos]
    have h3 : ξ₁ ^ 3 ≤ (4.3528745960 : ℝ) ^ 3 := pow_le_pow_left₀ hξ0 hb 3
    have n : (4.3528745960 : ℝ) ^ 3 ≤ 11.402542864 * (3 * 2.4110460120) := by norm_num
    linarith

/-- Lane–Emden equation θ'' + (2/ξ)θ' + θ² = 0: for every solution θ on (0, 5] with θ(0) = 1, θ
differentiable on [0, 5] with derivative φ, and φ continuous at 0, there is a first zero ξ₁ of θ with
4.3528745959 ≤ ξ₁ ≤ 4.3528745960, at which −ξ₁² θ'(ξ₁) lies between 2.4110460120 and 2.4110460122
and ξ₁³/(3 · (−ξ₁² θ'(ξ₁))) lies between 11.402542860 and 11.402542864. -/
theorem laneEmden2_constants (θ φ : ℝ → ℝ)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) 5, HasDerivWithinAt θ (φ ξ) (Icc 0 5) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 5) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) 5, HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ 2) (Icc 0 5) ξ)
    (h0 : θ 0 = 1) :
    ∃ ξ₁ : ℝ, 4.3528745959 ≤ ξ₁ ∧ ξ₁ ≤ 4.3528745960 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      2.4110460120 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 2.4110460122 ∧
      11.402542860 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 11.402542864 := by
  have hsub : Icc (0 : ℝ) (9 / 2) ⊆ Icc 0 5 := Icc_subset_Icc le_rfl (by norm_num)
  exact core θ φ (fun ξ hξ => (hθ ξ (hsub hξ)).mono hsub) (hφ0.mono hsub)
    (fun ξ hξ => (hφ ξ ⟨hξ.1, by linarith [hξ.2]⟩).mono hsub) h0

end Checked.Math.LaneEmden2
