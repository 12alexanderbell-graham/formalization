import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Checked.Math.LE32Chain

/-!
# Mathematics (THE RESULT parts 1 and 5): the constants of the Lane–Emden polytrope of index three halves

**Question.** The Lane–Emden equation of index three halves, θ'' + (2/ξ) θ' + θ ^ (3/2) = 0 with
θ(0) = 1 (regular at the singular point ξ = 0), is the polytrope of a fully convective star and of
a cold non-relativistic degenerate gas. It has no closed-form solution. Its first zero ξ₁, the mass
factor −ξ₁ ^ 2 θ'(ξ₁) and the central concentration ξ₁ ^ 3/(3 · mass factor) are entries of the
classical tables of polytropes (Chandrasekhar; Horedt), computed there in floating point. Indices
two, three and four are certified (`Checked.Math.LaneEmden2`, `Checked.Math.LaneEmden`,
`Checked.Math.LaneEmden4`); a fractional index is new for the simulator: θ ^ (3/2) has no
polynomial Taylor recursion and is not smooth at the zero of θ.

**What is stated** (frozen before proof in `Work/Math/LaneEmden32.lean`, statement promoted
byte-identical): `laneEmden32_constants`, for every
θ, φ satisfying the hypotheses, the bounds on ξ₁, the mass factor and the central concentration
printed in its statement. θ'(0) = 0 is not assumed. The power is Mathlib's real power `Real.rpow`;
for a negative base it returns zero at this exponent, so past the zero of θ the hypothesis reads
θ'' + (2/ξ) θ' = 0; the conclusions concern [0, ξ₁], where θ is not negative. Only Mathlib
definitions occur in the statement. Existence of such a θ:
`Checked.Math.LE32Exists.exists_solution` (non-vacuity witness in `Checked/Trust/Witnesses.lean`).
-/

namespace Checked.Math.LaneEmden32
open Set

/-- The program's argument on [0, 183/50] (helper). -/
theorem core (θ φ : ℝ → ℝ)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) (183 / 50), HasDerivWithinAt θ (φ ξ) (Icc 0 (183 / 50)) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 (183 / 50)) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) (183 / 50),
      HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ ((3 : ℝ) / 2)) (Icc 0 (183 / 50)) ξ)
    (h0 : θ 0 = 1) :
    ∃ ξ₁ : ℝ, 3.65375373 ≤ ξ₁ ∧ ξ₁ ≤ 3.65375374 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      2.71405511 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 2.71405513 ∧
      5.99070450 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 5.99070453 := by
  have hφg : ∀ ξ ∈ Ioc (0 : ℝ) (183 / 50),
      HasDerivWithinAt φ (-(2 / ξ * φ ξ) - Checked.Math.LE32Cell.g32 (θ ξ)) (Icc 0 (183 / 50)) ξ :=
    fun ξ hξ => by rw [← Checked.Math.LE32Cell.rpow32_eq]; exact hφ ξ hξ
  obtain ⟨hneg, hlo, hhi, hom⟩ := Checked.Math.LE32Certs.chain hθ hφ0 hφg h0
  have hcont : ContinuousOn θ (Icc 0 (183 / 50)) := fun x hx => (hθ x hx).continuousWithinAt
  have hanti : StrictAntiOn θ (Icc 0 (3653753737 / 1000000000 : ℝ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 _)
      (hcont.mono (Icc_subset_Icc le_rfl (by norm_num)))
    intro x hx
    rw [interior_Icc] at hx
    have hx4 : x ∈ Ioo (0 : ℝ) (183 / 50) := ⟨hx.1, by linarith [hx.2]⟩
    have hd : HasDerivAt θ (φ x) x :=
      (hθ x (Ioo_subset_Icc_self hx4)).hasDerivAt (Icc_mem_nhds hx4.1 hx4.2)
    rw [hd.deriv]
    exact hneg x ⟨hx.1, hx.2.le⟩
  obtain ⟨ξ₁, hξ₁, hz⟩ : ∃ ξ₁ ∈ Icc (730750747 / 200000000 : ℝ) (3653753737 / 1000000000),
      θ ξ₁ = 0 := by
    have := intermediate_value_Icc' (show (730750747 / 200000000 : ℝ) ≤ 3653753737 / 1000000000
      by norm_num) (hcont.mono (Icc_subset_Icc (by norm_num) (by norm_num)))
    exact this ⟨hhi.le, hlo.le⟩
  obtain ⟨ho1, ho2⟩ := hom ξ₁ hξ₁
  have ha : (3.65375373 : ℝ) ≤ ξ₁ := by norm_num at hξ₁ ⊢; linarith [hξ₁.1]
  have hb : ξ₁ ≤ (3.65375374 : ℝ) := by norm_num at hξ₁ ⊢; linarith [hξ₁.2]
  have ha' : (730750747 / 200000000 : ℝ) ≤ ξ₁ := hξ₁.1
  have hb' : ξ₁ ≤ (3653753737 / 1000000000 : ℝ) := hξ₁.2
  have hω1 : (2.71405511 : ℝ) ≤ -(ξ₁ ^ 2 * φ ξ₁) := by norm_num at ho1 ⊢; linarith
  have hω2 : -(ξ₁ ^ 2 * φ ξ₁) ≤ (2.71405513 : ℝ) := by norm_num at ho2 ⊢; linarith
  have hξ0 : 0 ≤ ξ₁ := by linarith
  have hωpos : 0 < 3 * -(ξ₁ ^ 2 * φ ξ₁) := by linarith
  refine ⟨ξ₁, ha, hb, hz, fun ξ hξ => ?_, hω1, hω2, ?_, ?_⟩
  · have hlt := hanti ⟨hξ.1, le_trans hξ.2.le hξ₁.2⟩ ⟨by linarith [hξ₁.1], hξ₁.2⟩ hξ.2
    rw [hz] at hlt
    exact hlt
  · rw [le_div_iff₀ hωpos]
    have h3 : (730750747 / 200000000 : ℝ) ^ 3 ≤ ξ₁ ^ 3 := pow_le_pow_left₀ (by norm_num) ha' 3
    have n : (5.99070450 : ℝ) * (3 * (2714055121 / 1000000000)) ≤ (730750747 / 200000000) ^ 3 := by
      norm_num
    norm_num at ho2
    nlinarith
  · rw [div_le_iff₀ hωpos]
    have h3 : ξ₁ ^ 3 ≤ (3653753737 / 1000000000 : ℝ) ^ 3 := pow_le_pow_left₀ hξ0 hb' 3
    have n : (3653753737 / 1000000000 : ℝ) ^ 3 ≤ 5.99070453 * (3 * (2714055119 / 1000000000)) := by
      norm_num
    norm_num at ho1
    nlinarith

/-- Lane–Emden equation θ'' + (2/ξ)θ' + θ ^ (3/2) = 0: for every solution θ on (0, 4] with
θ(0) = 1, θ differentiable on [0, 4] with derivative φ, and φ continuous at 0, there is a zero ξ₁ of
θ with 3.65375373 ≤ ξ₁ ≤ 3.65375374 and θ > 0 on [0, ξ₁), at which −ξ₁² θ'(ξ₁) lies between
2.71405511 and 2.71405513 and ξ₁³/(3 · (−ξ₁² θ'(ξ₁))) lies between 5.99070450 and 5.99070453. -/
theorem laneEmden32_constants (θ φ : ℝ → ℝ)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) 4, HasDerivWithinAt θ (φ ξ) (Icc 0 4) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 4) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) 4,
      HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ ((3 : ℝ) / 2)) (Icc 0 4) ξ)
    (h0 : θ 0 = 1) :
    ∃ ξ₁ : ℝ, 3.65375373 ≤ ξ₁ ∧ ξ₁ ≤ 3.65375374 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      2.71405511 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 2.71405513 ∧
      5.99070450 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 5.99070453 := by
  have hsub : Icc (0 : ℝ) (183 / 50) ⊆ Icc 0 4 := Icc_subset_Icc le_rfl (by norm_num)
  exact core θ φ (fun ξ hξ => (hθ ξ (hsub hξ)).mono hsub) (hφ0.mono hsub)
    (fun ξ hξ => (hφ ξ ⟨hξ.1, by linarith [hξ.2]⟩).mono hsub) h0

end Checked.Math.LaneEmden32
