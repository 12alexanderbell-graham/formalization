import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Bonnor–Ebert sphere, `BEHTail`: the lower bound on the sublevel set of Volterra's function. If
V(u, v) = u + v − log u − 2 log(v/2) does not exceed its value at the certified state at radius 150, then
u v³ > 6.059 (above 4π times the square of 0.694367). One application of the tangent-line inequality for
the logarithm per variable, with negative slopes (convex duality from below). Written by run
2026-11-14T0428Z. -/

namespace Work.Math.BEHTail
open Set

/-- Tangent-line bound for x − 1 − log x, for every slope parameter a > −1. -/
theorem dual' {x a : ℝ} (hx : 0 < x) (ha : -1 < a) :
    a * Real.log x + a - (1 + a) * Real.log (1 + a) ≤ x - 1 - Real.log x := by
  have h1 : 0 < 1 + a := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hx h1)
  rw [Real.log_div hx.ne' h1.ne'] at h
  have h2 : (1 + a) * (Real.log x - Real.log (1 + a)) ≤ (1 + a) * (x / (1 + a) - 1) :=
    mul_le_mul_of_nonneg_left h h1.le
  have h3 : (1 + a) * (x / (1 + a) - 1) = x - 1 - a := by field_simp; ring
  nlinarith

theorem log_19 : Real.log (19 / 20) ≤ -512932 / 10000000 := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(1 / 20 : ℝ)| < 1 by norm_num [abs_lt]) 10
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  linarith [h.1, h.2]

theorem log_37 : Real.log (37 / 40) ≤ -779615 / 10000000 := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(3 / 40 : ℝ)| < 1 by norm_num [abs_lt]) 10
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  linarith [h.1, h.2]

theorem log_K : Real.log (6059 / 8000) ≤ -2778967 / 10000000 := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(1941 / 8000 : ℝ)| < 1 by norm_num [abs_lt]) 16
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  linarith [h.1, h.2]

theorem log_u150 : 512208 / 10000000 ≤ Real.log (10525553455 / 10000000000) := by
  have h := Real.abs_log_sub_add_sum_range_le
    (show |(-525553455 / 10000000000 : ℝ)| < 1 by norm_num [abs_lt]) 10
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  linarith [h.1, h.2]

theorem log_v150 : -696614 / 10000000 ≤ Real.log (9327096116 / 10000000000) := by
  have h := Real.abs_log_sub_add_sum_range_le
    (show |(672903884 / 10000000000 : ℝ)| < 1 by norm_num [abs_lt]) 10
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  linarith [h.1, h.2]

/-- On the sublevel set of Volterra's function through the certified state at radius 150,
u v³ > 6.059. -/
theorem uv_lower {u v u0 v0 : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hu0 : 10525553455 / 10000000000 ≤ u0) (hu0' : u0 ≤ 10525557455 / 10000000000)
    (hv0 : 18654192232 / 10000000000 ≤ v0) (hv0' : v0 ≤ 18654196232 / 10000000000)
    (hV : u + v - Real.log u - 2 * Real.log (v / 2) ≤
      u0 + v0 - Real.log u0 - 2 * Real.log (v0 / 2)) :
    6059 / 1000 < u * v ^ 3 := by
  have hv2 : 0 < v / 2 := by positivity
  have d1 := dual' hu (show (-1 : ℝ) < -1 / 20 by norm_num)
  have d2 := dual' hv2 (show (-1 : ℝ) < -3 / 40 by norm_num)
  norm_num at d1 d2
  have hprod : Real.log (u * v ^ 3 / 8) = Real.log u + 3 * Real.log (v / 2) := by
    have : u * v ^ 3 / 8 = u * (v / 2) ^ 3 := by ring
    rw [this, Real.log_mul hu.ne' (by positivity), Real.log_pow]
    push_cast; ring
  have l19 := log_19
  have l37 := log_37
  have lK := log_K
  have lu0 : Real.log (10525553455 / 10000000000) ≤ Real.log u0 := Real.log_le_log (by norm_num) hu0
  have lv0 : Real.log (9327096116 / 10000000000) ≤ Real.log (v0 / 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have lu := log_u150
  have lv := log_v150
  have key : Real.log (6059 / 8000) < Real.log (u * v ^ 3 / 8) := by
    rw [hprod]; linarith
  have h8 := (Real.log_lt_log_iff (by norm_num) (by positivity)).1 key
  linarith

end Work.Math.BEHTail
