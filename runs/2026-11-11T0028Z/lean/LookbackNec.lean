import Checked.Trust.NonVacuity
import Checked.Cosmography.LookbackThird
import Mathlib.Analysis.Calculus.ContDiff.Operations

open Filter Topology Asymptotics
namespace Checked.Trust.NCB
open Checked.Cosmography

/-- With a vanishing present scale factor the redshift is −1 for every emission time (junk division). -/
theorem redshift_of_a0 (a : ℝ → ℝ) (t₀ : ℝ) (h0 : a t₀ = 0) (t : ℝ) : redshift a t₀ t = -1 := by
  simp [redshift, h0]

/-- `a t₀ ≠ 0` is redundant in the second-order lookback expansion (Lean's total division): if
a(t₀) = 0 the redshift is −1 and the Hubble rate 0, so the remainder is t₀ − t, which is o(1). -/
theorem lookback_second_order_r3 : dropped% Checked.Cosmography.lookback_second_order 3 := by
  intro a t₀ ha ha' hH
  by_cases h0 : a t₀ = 0
  · have e2 : hubble a t₀ = 0 := by simp [hubble, h0]
    simp only [redshift_of_a0 a t₀ h0, e2, div_zero, sub_zero]
    norm_num
    have : Tendsto (fun t : ℝ => t₀ - t) (𝓝 t₀) (𝓝 (t₀ - t₀)) := tendsto_const_nhds.sub tendsto_id
    simpa using this
  · exact Checked.Cosmography.lookback_second_order a t₀ ha ha' h0 hH

/-- The same for the big-O form with a cubic remainder: the remainder t₀ − t is bounded. -/
theorem lookback_second_order_bigO_r2 : dropped% Checked.Cosmography.lookback_second_order_bigO 2 := by
  intro a t₀ ha hH
  by_cases h0 : a t₀ = 0
  · have e2 : hubble a t₀ = 0 := by simp [hubble, h0]
    simp only [redshift_of_a0 a t₀ h0, e2, div_zero, sub_zero]
    norm_num
    have : Tendsto (fun t : ℝ => t₀ - t) (𝓝 t₀) (𝓝 (t₀ - t₀)) := tendsto_const_nhds.sub tendsto_id
    exact this.abs.isBoundedUnder_le
  · exact Checked.Cosmography.lookback_second_order_bigO a t₀ ha h0 hH

/-- The scale factor 1 + t² (zero velocity at t = 0). -/
noncomputable def flatStart (t : ℝ) : ℝ := 1 + t ^ 2

theorem flatStart_deriv : deriv flatStart = fun t => 2 * t := by
  funext t
  have h : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).const_add 1
  exact h.deriv

/-- No bound |t| ≤ C t² holds near 0. -/
theorem not_abs_le_sq (C : ℝ) : ¬ ∀ᶠ t in 𝓝 (0 : ℝ), |t| ≤ C * t ^ 2 := by
  intro hC
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hC
  set c := |C| + 1
  have hc : 0 < c := by positivity
  set t := min (δ / 2) (1 / (2 * c))
  have ht : 0 < t := lt_min (by linarith) (by positivity)
  have ht1 : t ≤ 1 / (2 * c) := min_le_right _ _
  have htδ : t ≤ δ / 2 := min_le_left _ _
  have hd : dist t 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos ht]; linarith
  have key := hball hd
  rw [abs_of_pos ht] at key
  have hct : c * t ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left ht1 hc.le
    rwa [show c * (1 / (2 * c)) = 1 / 2 by field_simp] at this
  have hC : C * t ^ 2 ≤ c * t ^ 2 := by
    have := le_abs_self C; nlinarith [sq_nonneg t]
  nlinarith

/-- The redshift of 1 + t² at observation time 0: z = −t²/(1 + t²), so |z| ≤ t². -/
theorem flatStart_z (t : ℝ) : |redshift flatStart 0 t| ≤ t ^ 2 := by
  have hz : redshift flatStart 0 t = -(t ^ 2 / (1 + t ^ 2)) := by
    simp [redshift, flatStart]; field_simp; ring
  rw [hz, abs_neg, abs_of_nonneg (by positivity)]
  exact div_le_self (by positivity) (by nlinarith [sq_nonneg t])

/-- For 1 + t², the function −t is not O(z³) at 0, where z is the redshift. -/
theorem flatStart_not_bigO :
    ¬ (fun t : ℝ => (0 : ℝ) - t) =O[𝓝 0] (fun t => redshift flatStart 0 t ^ 3) := by
  intro h
  obtain ⟨C, hC⟩ := h.bound
  apply not_abs_le_sq (|C|)
  filter_upwards [hC, Metric.ball_mem_nhds (0 : ℝ) one_pos] with t ht ht1
  simp only [zero_sub, norm_neg, Real.norm_eq_abs, abs_pow] at ht
  have hz := flatStart_z t
  have ht1' : |t| < 1 := by simpa [Real.dist_eq] using ht1
  have hsq : t ^ 2 ≤ 1 := by nlinarith [abs_nonneg t, sq_abs t]
  have h3 : |redshift flatStart 0 t| ^ 3 ≤ t ^ 2 := by
    have h0 := abs_nonneg (redshift flatStart 0 t)
    calc |redshift flatStart 0 t| ^ 3 ≤ (t ^ 2) ^ 3 := pow_le_pow_left₀ h0 hz 3
      _ ≤ t ^ 2 := by nlinarith [pow_le_one₀ (sq_nonneg t) hsq (n := 2), sq_nonneg t]
  calc |t| ≤ C * |redshift flatStart 0 t| ^ 3 := ht
    _ ≤ |C| * |redshift flatStart 0 t| ^ 3 := by
        gcongr; exact le_abs_self C
    _ ≤ |C| * t ^ 2 := by gcongr

/-- For 1 + t², the function −t is not o(z²) at 0. -/
theorem flatStart_not_littleO :
    ¬ (fun t : ℝ => (0 : ℝ) - t) =o[𝓝 0] (fun t => redshift flatStart 0 t ^ 2) := by
  intro h
  apply not_abs_le_sq 1
  filter_upwards [h.bound one_pos, Metric.ball_mem_nhds (0 : ℝ) one_pos] with t ht ht1
  simp only [zero_sub, norm_neg, Real.norm_eq_abs, abs_pow] at ht
  have hz := flatStart_z t
  have ht1' : |t| < 1 := by simpa [Real.dist_eq] using ht1
  have hsq : t ^ 2 ≤ 1 := by nlinarith [abs_nonneg t, sq_abs t]
  have h2 : |redshift flatStart 0 t| ^ 2 ≤ t ^ 2 := by
    have h0 := abs_nonneg (redshift flatStart 0 t)
    calc |redshift flatStart 0 t| ^ 2 ≤ (t ^ 2) ^ 2 := pow_le_pow_left₀ h0 hz 2
      _ ≤ t ^ 2 := by nlinarith [sq_nonneg t]
  linarith

/-- `deriv a t₀ ≠ 0` is needed in the big-O lookback expansion: a = 1 + t² at t₀ = 0. -/
theorem lookback_second_order_bigO_h3 : necessity% Checked.Cosmography.lookback_second_order_bigO 3 := by
  refine ⟨flatStart, 0, (show ContDiff ℝ 3 flatStart from ContDiff.add contDiff_const (contDiff_id.pow 2)).contDiffAt, by simp [flatStart], ?_⟩
  have hd : deriv flatStart 0 = 0 := by rw [flatStart_deriv]; ring
  have hH : hubble flatStart 0 = 0 := by simp [hubble, hd]
  rw [hH]; simp only [div_zero, sub_zero]
  exact flatStart_not_bigO

/-- `deriv a t₀ ≠ 0` is needed in the little-o lookback expansion: a = 1 + t² at t₀ = 0. -/
theorem lookback_second_order_h4 : necessity% Checked.Cosmography.lookback_second_order 4 := by
  have hdiff : Differentiable ℝ flatStart := by unfold flatStart; fun_prop
  refine ⟨flatStart, 0, Eventually.of_forall fun t => hdiff t, ?_, by simp [flatStart], ?_⟩
  · rw [flatStart_deriv]; fun_prop
  · have hd : deriv flatStart 0 = 0 := by rw [flatStart_deriv]; ring
    have hH : hubble flatStart 0 = 0 := by simp [hubble, hd]
    rw [hH]; simp only [div_zero, sub_zero]
    exact flatStart_not_littleO

end Checked.Trust.NCB
