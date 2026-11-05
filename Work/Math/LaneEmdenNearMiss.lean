import Mathlib
import Checked.Math.LaneEmden
import Checked.Math.LEExists

/-!
# Audit of `Checked.Math.LaneEmden.laneEmden3_constants`: near misses and mutants fail

Run 2026-11-05T0428Z (written in the auditor role while run 0228Z held the LOCK, annex 48.4). Fidelity audit items
"bites on examples" and "near-misses fail" (annex XL): each theorem below takes the frozen
statement, changes one thing, and proves the changed statement FALSE.

1. `near_miss_initial`: the initial value θ(0) = 1 changed by 10⁻⁸ (θ(0) = 1 − 10⁻⁸). By the
   scaling symmetry θ ↦ A θ(A ξ) of the n = 3 equation, the scaled solution has its first zero
   at ξ₁/A, which lies outside the frozen interval. So the stated interval is tight enough to
   detect a relative error of 10⁻⁸ in the initial condition.
2. `mutant_n5`: exponent 3 changed to 5. The n = 5 solution (1 + ξ²/3)^(−1/2) has no zero.
3. `mutant_n1`: exponent 3 changed to 1. The n = 1 solution sinc ξ = sin ξ / ξ has its zeros at
   kπ; none lies in the frozen interval (2π < 6.89 < 3π).

Not refutable (recorded in the run README): dropping `hφ0` (continuity of θ' at 0) — it follows
from the other hypotheses (the blind bridge derives it).
-/

namespace Work.Math.LaneEmdenNearMiss
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
  Checked.Math.LaneEmden.laneEmden3_constants θ φ hθ hφ0 hφ h0

/-- Near miss: the frozen statement with θ(0) = 1 − 10⁻⁸ instead of θ(0) = 1 is false. -/
theorem near_miss_initial : ¬ ∀ θ φ : ℝ → ℝ,
    (∀ ξ ∈ Icc (0 : ℝ) 7, HasDerivWithinAt θ (φ ξ) (Icc 0 7) ξ) →
    ContinuousWithinAt φ (Icc 0 7) 0 →
    (∀ ξ ∈ Ioc (0 : ℝ) 7, HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ 3) (Icc 0 7) ξ) →
    θ 0 = 1 - 1 / 10 ^ 8 → Concl θ φ := by
  intro H
  obtain ⟨θ, φ, hθ, hφ0, hφ, h0⟩ := Checked.Math.LEExists.exists_solution
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

section N1
open Real Filter Topology

/-- Derivative of sinc. -/
noncomputable def φ1 (x : ℝ) : ℝ := if x = 0 then 0 else (x * cos x - sin x) / x ^ 2

theorem sinc_eventually {x : ℝ} (hx : x ≠ 0) : sinc =ᶠ[𝓝 x] fun y => sin y / y := by
  filter_upwards [isOpen_ne.mem_nhds hx] with y hy using sinc_of_ne_zero hy

theorem hasDerivAt_sinc_ne {x : ℝ} (hx : x ≠ 0) : HasDerivAt sinc (φ1 x) x := by
  have h := (hasDerivAt_sin x).div (hasDerivAt_id x) hx
  have h' := h.congr_of_eventuallyEq (sinc_eventually hx)
  convert h' using 1
  simp only [φ1, if_neg hx, id]
  field_simp

/-- |x cos x − sin x| ≤ |x|³ for |x| ≤ 1. -/
theorem num_bound {x : ℝ} (hx : |x| ≤ 1) : |x * cos x - sin x| ≤ |x| ^ 3 := by
  have hc := cos_bound hx
  have hs := sin_bound hx
  have e : x * cos x - sin x =
      x * (cos x - (1 - x ^ 2 / 2)) - (sin x - (x - x ^ 3 / 6)) - x ^ 3 / 3 := by ring
  rw [e]
  have ha : 0 ≤ |x| := abs_nonneg x
  have h1 : |x * (cos x - (1 - x ^ 2 / 2))| ≤ |x| * (|x| ^ 4 * (5 / 96)) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hc ha
  have h3 : |x ^ 3 / 3| = |x| ^ 3 / 3 := by rw [abs_div, abs_pow]; norm_num
  have t1 := abs_sub (x * (cos x - (1 - x ^ 2 / 2)) - (sin x - (x - x ^ 3 / 6))) (x ^ 3 / 3)
  have t2 := abs_sub (x * (cos x - (1 - x ^ 2 / 2))) (sin x - (x - x ^ 3 / 6))
  have p5 : |x| ^ 5 ≤ |x| ^ 3 := pow_le_pow_of_le_one ha hx (by norm_num)
  have e5 : |x| * (|x| ^ 4 * (5 / 96)) = |x| ^ 5 * (5 / 96) := by ring
  rw [e5] at h1
  have p3 : 0 ≤ |x| ^ 3 := pow_nonneg ha 3
  linarith

theorem abs_φ1_le {x : ℝ} (hx : |x| ≤ 1) : |φ1 x| ≤ |x| := by
  by_cases h0 : x = 0
  · simp [φ1, h0]
  · simp only [φ1, if_neg h0]
    have hp : 0 < |x| := abs_pos.2 h0
    rw [abs_div, abs_pow, div_le_iff₀ (by positivity)]
    have := num_bound hx
    calc |x * cos x - sin x| ≤ |x| ^ 3 := this
      _ = |x| * |x| ^ 2 := by ring

theorem continuousAt_φ1 : ContinuousAt φ1 0 := by
  rw [ContinuousAt, show φ1 0 = 0 by simp [φ1]]
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hlim : Tendsto (fun x : ℝ => |x|) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs.tendsto (0 : ℝ))
  refine squeeze_zero' (Eventually.of_forall fun x => abs_nonneg _) ?_ hlim
  have : ∀ᶠ x in 𝓝 (0 : ℝ), |x| ≤ 1 := by
    have := Metric.ball_mem_nhds (0 : ℝ) one_pos
    filter_upwards [this] with x hx
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
    exact hx.le
  filter_upwards [this] with x hx using abs_φ1_le hx

/-- Right derivative of sinc at 0 is 0 (within [0, ∞)). -/
theorem hasDerivWithinAt_sinc_zero : HasDerivWithinAt sinc (φ1 0) (Ici 0) 0 := by
  rw [show φ1 0 = 0 by simp [φ1], hasDerivWithinAt_iff_tendsto_slope]
  have hlim : Tendsto (fun x : ℝ => |x|) (𝓝[Ici 0 \ {0}] 0) (𝓝 0) := by
    have := (continuous_abs.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ici 0 \ {0}))
    simpa using this
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun x => abs_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx.2)
  show |slope sinc 0 x| ≤ |x|
  rw [slope_def_field, sinc_zero, sub_zero, sinc_of_ne_zero hx0.ne']
  have h1 := sin_lt hx0
  have h2 := sin_gt_sub_cube hx0
  rw [abs_of_pos hx0, abs_le]
  constructor
  · rw [le_div_iff₀ hx0, div_sub_one hx0.ne', le_div_iff₀ hx0]
    nlinarith
  · rw [div_le_iff₀ hx0, div_sub_one hx0.ne', div_le_iff₀ hx0]
    nlinarith

theorem deriv_φ1 {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt φ1 (-(2 / x * φ1 x) - sinc x) x := by
  have hev : φ1 =ᶠ[𝓝 x] fun y => (y * cos y - sin y) / y ^ 2 := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    simp [φ1, hy]
  have hN : HasDerivAt (fun y => y * cos y - sin y) (1 * cos x + x * -sin x - cos x) x :=
    ((hasDerivAt_id x).mul (hasDerivAt_cos x)).sub (hasDerivAt_sin x)
  have hD : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have h := (hN.div hD (pow_ne_zero 2 hx)).congr_of_eventuallyEq hev
  convert h using 1
  simp only [φ1, if_neg hx, sinc_of_ne_zero hx]
  field_simp
  ring

/-- Mutant: the frozen statement with θ in place of θ³ (index n = 1) is false. -/
theorem mutant_n1 : ¬ ∀ θ φ : ℝ → ℝ,
    (∀ ξ ∈ Icc (0 : ℝ) 7, HasDerivWithinAt θ (φ ξ) (Icc 0 7) ξ) →
    ContinuousWithinAt φ (Icc 0 7) 0 →
    (∀ ξ ∈ Ioc (0 : ℝ) 7, HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ) (Icc 0 7) ξ) →
    θ 0 = 1 → Concl θ φ := by
  intro H
  have dθ : ∀ ξ ∈ Icc (0 : ℝ) 7, HasDerivWithinAt sinc (φ1 ξ) (Icc 0 7) ξ := by
    intro ξ hξ
    rcases eq_or_ne ξ 0 with h | h
    · subst h; exact hasDerivWithinAt_sinc_zero.mono Icc_subset_Ici_self
    · exact (hasDerivAt_sinc_ne h).hasDerivWithinAt
  obtain ⟨ξ₁, h1, h2, hz, -⟩ := H sinc φ1 dθ continuousAt_φ1.continuousWithinAt
    (fun ξ hξ => (deriv_φ1 hξ.1.ne').hasDerivWithinAt) sinc_zero
  have hp : 0 < ξ₁ := by linarith
  rw [sinc_of_ne_zero hp.ne'] at hz
  have hs : sin ξ₁ = 0 := by
    rcases div_eq_zero_iff.1 hz with h | h
    · exact h
    · exact absurd h hp.ne'
  -- 2π < ξ₁ < 3π, so sin ξ₁ = sin (ξ₁ − 2π) > 0
  have hpi1 := pi_gt_three
  have hpi2 := pi_lt_d2
  have : 0 < sin (ξ₁ - 2 * π) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [sin_sub_two_pi] at this
  linarith

end N1

end Work.Math.LaneEmdenNearMiss

#print axioms Work.Math.LaneEmdenNearMiss.near_miss_initial
#print axioms Work.Math.LaneEmdenNearMiss.mutant_n5
#print axioms Work.Math.LaneEmdenNearMiss.mutant_n1
