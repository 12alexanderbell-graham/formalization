import Checked.Math.BEHTail

/-! Bonnor–Ebert sphere, `BEOTail`: the lower bound of u v³ on the sublevel set of Volterra's function
through the certified state at radius 20000 (end of the one-sided cells of `BEOCell`), by the tangent-line
inequality for the logarithm with negative slopes (convex duality from below, as in
`Checked.Math.BEHTail`). -/

namespace Work.Math.BEOTail
open Set Checked.Math.BEHTail

theorem log_a1 : 5671348 / 1000000000 ≤ Real.log (10056874610 / 10000000000) := by
  have h := Real.abs_log_sub_add_sum_range_le
    (show |(-5687461 / 1000000000 : ℝ)| < 1 by norm_num [abs_lt]) 10
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  linarith [h.1, h.2]

theorem log_a2 : -5475953 / 1000000000 ≤ Real.log (19890780260 / 20000000000) := by
  have h := Real.abs_log_sub_add_sum_range_le
    (show |(5460987 / 1000000000 : ℝ)| < 1 by norm_num [abs_lt]) 10
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  linarith [h.1, h.2]

theorem log_b1 : Real.log (249 / 250) ≤ -4008021 / 1000000000 := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(1 / 250 : ℝ)| < 1 by norm_num [abs_lt]) 10
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  linarith [h.1, h.2]

theorem log_b2 : Real.log (497 / 500) ≤ -6018072 / 1000000000 := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(3 / 500 : ℝ)| < 1 by norm_num [abs_lt]) 10
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  linarith [h.1, h.2]

theorem log_b3 : Real.log (7805 / 8000) ≤ -24676987 / 1000000000 := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(39 / 1600 : ℝ)| < 1 by norm_num [abs_lt]) 10
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  linarith [h.1, h.2]

/-- On the sublevel set of Volterra's function through the certified state at radius 20000, u v³ is
bounded below. -/
theorem uv_lower2 {u v u0 v0 : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hu0 : 10056874610 / 10000000000 ≤ u0) (hu0' : u0 ≤ 10056878610 / 10000000000)
    (hv0 : 19890780260 / 10000000000 ≤ v0) (hv0' : v0 ≤ 19890784260 / 10000000000)
    (hV : u + v - Real.log u - 2 * Real.log (v / 2) ≤
      u0 + v0 - Real.log u0 - 2 * Real.log (v0 / 2)) :
    7805 / 1000 < u * v ^ 3 := by
  have hv2 : 0 < v / 2 := by positivity
  have d1 := dual' hu (show (-1 : ℝ) < -1 / 250 by norm_num)
  have d2 := dual' hv2 (show (-1 : ℝ) < -3 / 500 by norm_num)
  norm_num at d1 d2
  have hprod : Real.log (u * v ^ 3 / 8) = Real.log u + 3 * Real.log (v / 2) := by
    have : u * v ^ 3 / 8 = u * (v / 2) ^ 3 := by ring
    rw [this, Real.log_mul hu.ne' (by positivity), Real.log_pow]
    push_cast; ring
  have l1 := log_b1
  have l2 := log_b2
  have l3 := log_b3
  have lu0 : Real.log (10056874610 / 10000000000) ≤ Real.log u0 := Real.log_le_log (by norm_num) hu0
  have lv0 : Real.log (19890780260 / 20000000000) ≤ Real.log (v0 / 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have lu := log_a1
  have lv := log_a2
  have key : Real.log (7805 / 8000) < Real.log (u * v ^ 3 / 8) := by
    rw [hprod]; linarith
  have h8 := (Real.log_lt_log_iff (by norm_num) (by positivity)).1 key
  linarith

end Work.Math.BEOTail
