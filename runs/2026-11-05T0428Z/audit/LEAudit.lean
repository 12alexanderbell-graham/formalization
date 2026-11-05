import Mathlib
import Work.Math.LaneEmden
import Work.Math.LEExists

/-!
# Audit of `Work.Math.LaneEmden.laneEmden3_constants`: near misses and mutants fail

Auditor run 2026-11-05T0428Z (annex 48.4: run 0228Z held the LOCK). Fidelity audit items
"bites on examples" and "near-misses fail" (annex XL): each theorem below takes the frozen
statement, changes one thing, and proves the changed statement FALSE.

1. `near_miss_initial`: the initial value θ(0) = 1 changed by 10⁻⁸ (θ(0) = 1 − 10⁻⁸). By the
   scaling symmetry θ ↦ A θ(A ξ) of the n = 3 equation, the scaled solution has its first zero
   at ξ₁/A, which lies outside the frozen interval. So the stated interval is tight enough to
   detect a relative error of 10⁻⁸ in the initial condition.
2. `mutant_n5`: exponent 3 changed to 5. The n = 5 solution (1 + ξ²/3)^(−1/2) has no zero.
-/

namespace Runs.LEAudit
open Set

/-- The frozen conclusion, as a predicate of (θ, φ). -/
def Concl (θ φ : ℝ → ℝ) : Prop :=
  ∃ ξ₁ : ℝ, 6.896848615 ≤ ξ₁ ∧ ξ₁ ≤ 6.896848625 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      2.018235945 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 2.018235955 ∧
      54.1824805 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 54.1824815

/-- Sanity: the frozen theorem is exactly "hypotheses → `Concl`". -/
theorem frozen_is (θ φ : ℝ → ℝ)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) 7, HasDerivWithinAt θ (φ ξ) (Icc 0 7) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 7) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) 7, HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ 3) (Icc 0 7) ξ)
    (h0 : θ 0 = 1) : Concl θ φ :=
  Work.Math.LaneEmden.laneEmden3_constants θ φ hθ hφ0 hφ h0

/-- Near miss: the frozen statement with θ(0) = 1 − 10⁻⁸ instead of θ(0) = 1 is false. -/
theorem near_miss_initial : ¬ ∀ θ φ : ℝ → ℝ,
    (∀ ξ ∈ Icc (0 : ℝ) 7, HasDerivWithinAt θ (φ ξ) (Icc 0 7) ξ) →
    ContinuousWithinAt φ (Icc 0 7) 0 →
    (∀ ξ ∈ Ioc (0 : ℝ) 7, HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ 3) (Icc 0 7) ξ) →
    θ 0 = 1 - 1 / 10 ^ 8 → Concl θ φ := by
  intro H
  obtain ⟨θ, φ, hθ, hφ0, hφ, h0⟩ := Work.Math.LEExists.exists_solution
  set A : ℝ := 1 - 1 / 10 ^ 8 with hA
  have hA0 : 0 < A := by norm_num [hA]
  have hA1 : A ≤ 1 := by norm_num [hA]
  clear_value A
  have maps : MapsTo (fun ξ : ℝ => A * ξ) (Icc 0 7) (Icc 0 7) := fun ξ hξ =>
    ⟨mul_nonneg hA0.le hξ.1, by nlinarith [hξ.1, hξ.2]⟩
  have hlin (ξ : ℝ) : HasDerivWithinAt (fun ξ : ℝ => A * ξ) A (Icc 0 7) ξ := by
    simpa using ((hasDerivAt_id ξ).const_mul A).hasDerivWithinAt
  have dψ : ∀ ξ ∈ Icc (0 : ℝ) 7,
      HasDerivWithinAt (fun ξ => A * θ (A * ξ)) (A ^ 2 * φ (A * ξ)) (Icc 0 7) ξ := by
    intro ξ hξ
    have h := ((hθ (A * ξ) (maps hξ)).comp ξ (hlin ξ) maps).const_mul A
    exact h.congr_deriv (by ring)
  have cχ : ContinuousWithinAt (fun ξ => A ^ 2 * φ (A * ξ)) (Icc 0 7) 0 := by
    have hc : ContinuousWithinAt (fun ξ : ℝ => A * ξ) (Icc 0 7) 0 :=
      (continuous_const.mul continuous_id).continuousWithinAt
    have h0' : ContinuousWithinAt φ (Icc 0 7) (A * 0) := by simpa using hφ0
    exact (h0'.comp hc maps).const_mul (A ^ 2)
  have dχ : ∀ ξ ∈ Ioc (0 : ℝ) 7,
      HasDerivWithinAt (fun ξ => A ^ 2 * φ (A * ξ))
        (-(2 / ξ * (A ^ 2 * φ (A * ξ))) - (A * θ (A * ξ)) ^ 3) (Icc 0 7) ξ := by
    intro ξ hξ
    have hAξ : A * ξ ∈ Ioc (0 : ℝ) 7 := ⟨mul_pos hA0 hξ.1, by nlinarith [hξ.1, hξ.2]⟩
    have h := ((hφ (A * ξ) hAξ).comp ξ (hlin ξ) maps).const_mul (A ^ 2)
    have hξ0 : ξ ≠ 0 := hξ.1.ne'
    refine h.congr_deriv ?_
    field_simp
  have hψ0 : A * θ (A * 0) = A := by simp [h0]
  obtain ⟨ξ', h1, h2, hz, -⟩ := H _ _ dψ cχ dχ hψ0
  -- θ (A ξ') = 0, but A ξ' < 6.896848615 ≤ ξ₁ and θ > 0 on [0, ξ₁)
  obtain ⟨ξ₁, hξ₁, -, -, hpos, -⟩ := frozen_is θ φ hθ hφ0 hφ h0
  have hz' : θ (A * ξ') = 0 := by
    have : A * θ (A * ξ') = 0 := hz
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hA0.ne'
    · exact h
  have hmem : A * ξ' ∈ Ico 0 ξ₁ := by
    refine ⟨mul_nonneg hA0.le (by linarith), ?_⟩
    have : A * ξ' ≤ A * 6.896848625 := mul_le_mul_of_nonneg_left h2 hA0.le
    have : A * (6.896848625 : ℝ) < 6.896848615 := by norm_num [hA]
    have h15 : (6.896848615 : ℝ) ≤ ξ₁ := hξ₁
    linarith
  have := hpos _ hmem
  rw [hz'] at this
  exact lt_irrefl _ this

/-- The n = 5 solution. -/
noncomputable def θ5 (ξ : ℝ) : ℝ := (Real.sqrt (1 + ξ ^ 2 / 3))⁻¹

/-- Its derivative. -/
noncomputable def φ5 (ξ : ℝ) : ℝ := -(ξ / 3 * θ5 ξ ^ 3)

theorem θ5_pos (ξ : ℝ) : 0 < θ5 ξ := by
  unfold θ5; positivity

theorem θ5_sq (ξ : ℝ) : θ5 ξ ^ 2 * (1 + ξ ^ 2 / 3) = 1 := by
  unfold θ5
  have hu : 0 < 1 + ξ ^ 2 / 3 := by positivity
  rw [inv_pow, Real.sq_sqrt hu.le]
  field_simp

theorem hasDerivAt_θ5 (ξ : ℝ) : HasDerivAt θ5 (φ5 ξ) ξ := by
  have hu : 0 < 1 + ξ ^ 2 / 3 := by positivity
  have hd : HasDerivAt (fun x : ℝ => 1 + x ^ 2 / 3) (2 * ξ / 3) ξ := by
    have := ((hasDerivAt_pow 2 ξ).div_const 3).const_add 1
    convert this using 1; push_cast; ring
  have hs := hd.sqrt hu.ne'
  have hsp : 0 < Real.sqrt (1 + ξ ^ 2 / 3) := Real.sqrt_pos.2 hu
  have hi := hs.inv hsp.ne'
  have e : -(2 * ξ / 3 / (2 * Real.sqrt (1 + ξ ^ 2 / 3))) / Real.sqrt (1 + ξ ^ 2 / 3) ^ 2
      = φ5 ξ := by
    unfold φ5 θ5
    generalize Real.sqrt (1 + ξ ^ 2 / 3) = s at hsp ⊢
    field_simp
  exact hi.congr_deriv e

theorem hasDerivAt_φ5 (ξ : ℝ) (hξ : ξ ≠ 0) :
    HasDerivAt φ5 (-(2 / ξ * φ5 ξ) - θ5 ξ ^ 5) ξ := by
  have h := (((hasDerivAt_id ξ).div_const 3).mul ((hasDerivAt_θ5 ξ).pow 3)).neg
  have hsq := θ5_sq ξ
  have e : -(1 / 3 * (θ5 ^ 3) ξ + id ξ / 3 * ((3 : ℕ) * θ5 ξ ^ (3 - 1) * φ5 ξ))
      = -(2 / ξ * φ5 ξ) - θ5 ξ ^ 5 := by
    simp only [φ5, id, Pi.pow_apply]
    push_cast
    field_simp
    linear_combination (3 * θ5 ξ ^ 3) * hsq
  exact h.congr_deriv e

/-- Mutant: the frozen statement with θ⁵ in place of θ³ is false (the n = 5 solution
(1 + ξ²/3)^(−1/2) satisfies every hypothesis and has no zero). -/
theorem mutant_n5 : ¬ ∀ θ φ : ℝ → ℝ,
    (∀ ξ ∈ Icc (0 : ℝ) 7, HasDerivWithinAt θ (φ ξ) (Icc 0 7) ξ) →
    ContinuousWithinAt φ (Icc 0 7) 0 →
    (∀ ξ ∈ Ioc (0 : ℝ) 7, HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ 5) (Icc 0 7) ξ) →
    θ 0 = 1 → Concl θ φ := by
  intro H
  have hc : Continuous φ5 := by
    have : Continuous θ5 := continuous_iff_continuousAt.2 fun x =>
      (hasDerivAt_θ5 x).continuousAt
    unfold φ5; fun_prop
  obtain ⟨ξ₁, -, -, hz, -⟩ := H θ5 φ5 (fun ξ _ => (hasDerivAt_θ5 ξ).hasDerivWithinAt)
    hc.continuousWithinAt (fun ξ hξ => (hasDerivAt_φ5 ξ hξ.1.ne').hasDerivWithinAt)
    (by simp [θ5])
  exact (θ5_pos ξ₁).ne' hz

end Runs.LEAudit

#print axioms Runs.LEAudit.near_miss_initial
#print axioms Runs.LEAudit.mutant_n5
