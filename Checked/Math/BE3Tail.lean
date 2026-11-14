import Checked.Math.BEH2Tail

/-! Bonnor–Ebert sphere, `BE3Tail`: the upper bound of u v³ on the sublevel set of Volterra's function through the certified state at the end radius of the one-sided cells of `BE3Data`, by the tangent-line inequality for the logarithm with positive slopes (convex duality from above, as in `BEH2Tail`). Promoted from `Work/Math/BE3Tail.lean`. -/

namespace Checked.Math.BE3Tail
open Set

theorem log_x1 : Real.log (1001 / 1000) ≤ 9995004 / 10000000000 := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(-1 / 1000 : ℝ)| < 1 by norm_num [abs_lt]) 8
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  linarith [h.1, h.2]

theorem log_x2 : Real.log (2003 / 2000) ≤ 14988762 / 10000000000 := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(-3 / 2000 : ℝ)| < 1 by norm_num [abs_lt]) 8
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  linarith [h.1, h.2]

theorem log_ul : -19968474 / 10000000000 ≤ Real.log (9980051450 / 10000000000) := by
  have h := Real.abs_log_sub_add_sum_range_le
    (show |(19948550 / 10000000000 : ℝ)| < 1 by norm_num [abs_lt]) 8
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  linarith [h.1, h.2]

theorem log_vh : 10267507 / 10000000000 ≤ Real.log (20020545560 / 20000000000) := by
  have h := Real.abs_log_sub_add_sum_range_le
    (show |(-20545560 / 20000000000 : ℝ)| < 1 by norm_num [abs_lt]) 8
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  linarith [h.1, h.2]

theorem log_X : 62305497 / 10000000000 ≤ Real.log (805 / 800) := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(-5 / 800 : ℝ)| < 1 by norm_num [abs_lt]) 10
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  linarith [h.1, h.2]

/-- On the sublevel set of Volterra's function through the certified state at radius 300000, u v³ is
bounded above. -/
theorem uv_upper3 {u v u0 v0 : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hu0 : 9980051450 / 10000000000 ≤ u0) (hu0' : u0 ≤ 1)
    (hv0 : 2 ≤ v0) (hv0' : v0 ≤ 20020545560 / 10000000000)
    (hV : u + v - Real.log u - 2 * Real.log (v / 2) ≤
      u0 + v0 - Real.log u0 - 2 * Real.log (v0 / 2)) :
    u * v ^ 3 < 805 / 100 := by
  have fu := Checked.Math.BEH2Tail.f_anti (show (0 : ℝ) < 9980051450 / 10000000000 by norm_num) hu0 hu0'
  have fv := Checked.Math.BEH2Tail.g_mono hv0 hv0'
  have hy : 0 < v / 2 := by positivity
  have d1 := Checked.Math.BEHTail.dual' hu (show (-1 : ℝ) < 1 / 1000 by norm_num)
  have d2 := Checked.Math.BEHTail.dual' hy (show (-1 : ℝ) < 3 / 2000 by norm_num)
  norm_num at d1 d2
  have hprod : Real.log (u * v ^ 3 / 8) = Real.log u + 3 * Real.log (v / 2) := by
    have : u * v ^ 3 / 8 = u * (v / 2) ^ 3 := by ring
    rw [this, Real.log_mul hu.ne' (by positivity), Real.log_pow]
    push_cast; ring
  have l1 := log_x1
  have l2 := log_x2
  have lu := log_ul
  have lv : 10267507 / 10000000000 ≤ Real.log ((20020545560 / 10000000000 : ℝ) / 2) := by
    have : (20020545560 / 10000000000 : ℝ) / 2 = 20020545560 / 20000000000 := by norm_num
    rw [this]; exact log_vh
  have lX := log_X
  have key : Real.log (u * v ^ 3 / 8) < Real.log (805 / 800) := by
    rw [hprod]; linarith
  have h8 := (Real.log_lt_log_iff (by positivity) (by norm_num)).1 key
  linarith

end Checked.Math.BE3Tail
