import Mathlib
import Work.Math.LE92Chain

/-!
# Mathematics (THE RESULT parts 1 and 5): the constants of the Lane–Emden polytrope of index nine halves

**Question.** The Lane–Emden equation of index nine halves, θ'' + (2/ξ) θ' + θ ^ (9/2) = 0 with
θ(0) = 1 (regular at the singular point ξ = 0), is a row of the classical tables of polytropes
(Chandrasekhar; Horedt), computed there in floating point. It has no closed-form solution. Its
first zero ξ₁, the mass factor −ξ₁ ^ 2 θ'(ξ₁) and the central concentration ξ₁ ^ 3/(3 · mass
factor) are the entries of that row. Indices two, three, four, three halves, five halves and seven
halves are certified (`Checked.Math.LaneEmden2`, `Checked.Math.LaneEmden`, `Checked.Math.LaneEmden4`,
`Checked.Math.LaneEmden32`, `Checked.Math.LaneEmden52`, `Checked.Math.LaneEmden72`); θ ^ (9/2) has no
polynomial Taylor recursion and is not smooth at the zero of θ (its fifth derivative in θ blows up
there). The first zero lies near 31.8, three times further out than at index seven halves.

**What is stated** (frozen before proof, run 2026-11-20T0428Z): `laneEmden92_constants`, for every
θ, φ satisfying the hypotheses, the bounds on ξ₁, the mass factor and the central concentration
printed in its statement. θ'(0) = 0 is not assumed. The power is Mathlib's real power `Real.rpow`;
for a negative base it returns zero at this exponent, so past the zero of θ the hypothesis reads
θ'' + (2/ξ) θ' = 0; the conclusions concern [0, ξ₁], where θ is not negative. Only Mathlib
definitions occur in the statement. Existence of such a θ: `Work.Math.LE92Exists.exists_solution`
(checked in a separate module).
Reference (floating point, not evidence): `runs/2026-11-20T0428Z/scripts/ref92.py` (40 digits) and
`ref92b.py` (a second integrator).

**Proof.** A chain of 146 validated cells from the singular start at ξ = 1/2 to the bracket
[31.8364631, 31.8364634] of the zero (`Work.Math.LE92Certs.chain`), in the weighted norm
max(|Δθ|, w |Δφ|) with w = 1, 4, 10, 20 from ξ = 0, 4, 8, 16 (`Work.Math.LE92Cell.cell`): in the
unweighted max norm the enclosure grows like e^ξ and reaches 3 · 10⁻⁴ at the zero.
-/

namespace Work.Math.LaneEmden92
open Set

/-- The program's argument on [0, 796/25] (helper). -/
theorem core (θ φ : ℝ → ℝ)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) (796 / 25), HasDerivWithinAt θ (φ ξ) (Icc 0 (796 / 25)) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 (796 / 25)) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) (796 / 25),
      HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ ((9 : ℝ) / 2)) (Icc 0 (796 / 25)) ξ)
    (h0 : θ 0 = 1) :
    ∃ ξ₁ : ℝ, 31.836463 ≤ ξ₁ ∧ ξ₁ ≤ 31.836464 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      1.7377988 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 1.7377989 ∧
      6189.4730 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 6189.4733 := by
  have hφg : ∀ ξ ∈ Ioc (0 : ℝ) (796 / 25),
      HasDerivWithinAt φ (-(2 / ξ * φ ξ) - Work.Math.LE92Cell.g92 (θ ξ)) (Icc 0 (796 / 25)) ξ :=
    fun ξ hξ => by rw [← Work.Math.LE92Cell.rpow92_eq]; exact hφ ξ hξ
  obtain ⟨hneg, hlo, hhi, hom⟩ := Work.Math.LE92Certs.chain hθ hφ0 hφg h0
  have hcont : ContinuousOn θ (Icc 0 (796 / 25)) := fun x hx => (hθ x hx).continuousWithinAt
  have hanti : StrictAntiOn θ (Icc 0 (159182317 / 5000000 : ℝ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 _)
      (hcont.mono (Icc_subset_Icc le_rfl (by norm_num)))
    intro x hx
    rw [interior_Icc] at hx
    have hx4 : x ∈ Ioo (0 : ℝ) (796 / 25) := ⟨hx.1, by linarith [hx.2]⟩
    have hd : HasDerivAt θ (φ x) x :=
      (hθ x (Ioo_subset_Icc_self hx4)).hasDerivAt (Icc_mem_nhds hx4.1 hx4.2)
    rw [hd.deriv]
    exact hneg x ⟨hx.1, hx.2.le⟩
  obtain ⟨ξ₁, hξ₁, hz⟩ : ∃ ξ₁ ∈ Icc (318364631 / 10000000 : ℝ) (159182317 / 5000000), θ ξ₁ = 0 := by
    have := intermediate_value_Icc' (show (318364631 / 10000000 : ℝ) ≤ (159182317 / 5000000) by norm_num)
      (hcont.mono (Icc_subset_Icc (by norm_num) (by norm_num)))
    exact this ⟨hhi.le, hlo.le⟩
  obtain ⟨ho1, ho2⟩ := hom ξ₁ hξ₁
  have ha : (31.836463 : ℝ) ≤ ξ₁ := by norm_num at hξ₁ ⊢; linarith [hξ₁.1]
  have hb : ξ₁ ≤ (31.836464 : ℝ) := by norm_num at hξ₁ ⊢; linarith [hξ₁.2]
  have ha' : (318364631 / 10000000 : ℝ) ≤ ξ₁ := hξ₁.1
  have hb' : ξ₁ ≤ (159182317 / 5000000 : ℝ) := hξ₁.2
  have hω1 : (1.7377988 : ℝ) ≤ -(ξ₁ ^ 2 * φ ξ₁) := by norm_num at ho1 ⊢; linarith
  have hω2 : -(ξ₁ ^ 2 * φ ξ₁) ≤ (1.7377989 : ℝ) := by norm_num at ho2 ⊢; linarith
  have hξ0 : 0 ≤ ξ₁ := by linarith
  have hωpos : 0 < 3 * -(ξ₁ ^ 2 * φ ξ₁) := by linarith
  refine ⟨ξ₁, ha, hb, hz, fun ξ hξ => ?_, hω1, hω2, ?_, ?_⟩
  · have hlt := hanti ⟨hξ.1, le_trans hξ.2.le hξ₁.2⟩ ⟨by linarith [hξ₁.1], hξ₁.2⟩ hξ.2
    rw [hz] at hlt
    exact hlt
  · rw [le_div_iff₀ hωpos]
    have h3 : (318364631 / 10000000 : ℝ) ^ 3 ≤ ξ₁ ^ 3 := pow_le_pow_left₀ (by norm_num) ha' 3
    have n : (6189.4730 : ℝ) * (3 * (1737798871 / 1000000000)) ≤ (318364631 / 10000000 : ℝ) ^ 3 := by
      norm_num
    norm_num at ho2
    nlinarith
  · rw [div_le_iff₀ hωpos]
    have h3 : ξ₁ ^ 3 ≤ (159182317 / 5000000 : ℝ) ^ 3 := pow_le_pow_left₀ hξ0 hb' 3
    have n : (159182317 / 5000000 : ℝ) ^ 3 ≤ 6189.4733 * (3 * (108612429 / 62500000)) := by
      norm_num
    norm_num at ho1
    nlinarith

/-- Lane–Emden equation of index 9/2: for every solution θ of θ'' + (2/ξ)θ' + θ ^ (9/2) = 0 on
(0, 32] with θ(0) = 1, θ differentiable on [0, 32] with derivative φ, and φ continuous at 0, there is
a first zero ξ₁ of θ with 31.836463 ≤ ξ₁ ≤ 31.836464 (θ > 0 before it), at which −ξ₁² θ'(ξ₁) lies
between 1.7377988 and 1.7377989 and ξ₁³/(3 · (−ξ₁² θ'(ξ₁))) lies between 6189.4730 and
6189.4733. -/
theorem laneEmden92_constants (θ φ : ℝ → ℝ)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) 32, HasDerivWithinAt θ (φ ξ) (Icc 0 32) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 32) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) 32,
      HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ ((9 : ℝ) / 2)) (Icc 0 32) ξ)
    (h0 : θ 0 = 1) :
    ∃ ξ₁ : ℝ, 31.836463 ≤ ξ₁ ∧ ξ₁ ≤ 31.836464 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      1.7377988 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 1.7377989 ∧
      6189.4730 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 6189.4733 := by
  have hsub : Icc (0 : ℝ) (796 / 25) ⊆ Icc 0 32 := Icc_subset_Icc le_rfl (by norm_num)
  exact core θ φ (fun ξ hξ => (hθ ξ (hsub hξ)).mono hsub) (hφ0.mono hsub)
    (fun ξ hξ => (hφ ξ ⟨hξ.1, by linarith [hξ.2]⟩).mono hsub) h0

end Work.Math.LaneEmden92
