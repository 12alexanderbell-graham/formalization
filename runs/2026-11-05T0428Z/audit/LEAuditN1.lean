import Mathlib

/-!
# Audit of `laneEmden3_constants`, mutant n = 1 (θ in place of θ³)

The n = 1 solution is sinc ξ = sin ξ / ξ, first zero π. With θ in place of θ³ the frozen
statement is false. (Self-contained: imports only Mathlib; the frozen conclusion is copied
verbatim as `Concl`.)
-/

namespace Runs.LEAuditN1
open Set Real Filter Topology

/-- The frozen conclusion (verbatim copy). -/
def Concl (θ φ : ℝ → ℝ) : Prop :=
  ∃ ξ₁ : ℝ, 6.896848615 ≤ ξ₁ ∧ ξ₁ ≤ 6.896848625 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      2.018235945 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 2.018235955 ∧
      54.1824805 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 54.1824815

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

end Runs.LEAuditN1

#print axioms Runs.LEAuditN1.mutant_n1
