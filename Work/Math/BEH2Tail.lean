import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Checked.Math.BEHTail

/-! Bonnor–Ebert sphere, `BEH2Tail`: the upper bound of u v³ on the sublevel set of Volterra's function through
the certified state at the end radius of the cells of `BEH2Data`, by the tangent-line inequality for the
logarithm with positive slopes (convex duality from above). -/

namespace Work.Math.BEH2Tail
open Set

theorem log_81 : Real.log (81 / 80) ≤ 124226 / 10000000 := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(-1 / 80 : ℝ)| < 1 by norm_num [abs_lt]) 8
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  linarith [h.1, h.2]

theorem log_163 : Real.log (163 / 160) ≤ 185764 / 10000000 := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(-3 / 160 : ℝ)| < 1 by norm_num [abs_lt]) 8
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  linarith [h.1, h.2]

theorem log_ul : -197679 / 10000000 ≤ Real.log (9804262057 / 10000000000) := by
  have h := Real.abs_log_sub_add_sum_range_le
    (show |(195737943 / 10000000000 : ℝ)| < 1 by norm_num [abs_lt]) 8
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  linarith [h.1, h.2]

theorem log_vh : 162963 / 10000000 ≤ Real.log (20328598293 / 20000000000) := by
  have h := Real.abs_log_sub_add_sum_range_le
    (show |(-328598293 / 20000000000 : ℝ)| < 1 by norm_num [abs_lt]) 8
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  linarith [h.1, h.2]

theorem log_X : 781177 / 10000000 ≤ Real.log (865 / 800) := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(-65 / 800 : ℝ)| < 1 by norm_num [abs_lt]) 14
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  linarith [h.1, h.2]

/-- x − log x is antitone on (0, 1]. -/
theorem f_anti {a x : ℝ} (ha : 0 < a) (hax : a ≤ x) (hx : x ≤ 1) : x - Real.log x ≤ a - Real.log a := by
  have hx0 : 0 < x := by linarith
  have h := Real.log_le_sub_one_of_pos (show 0 < a / x by positivity)
  rw [Real.log_div ha.ne' hx0.ne'] at h
  have e : a / x * x = a := by field_simp
  have k : (x - a) + (a / x - 1) ≤ 0 := by
    have m : ((x - a) + (a / x - 1)) * x = (x - a) * (x - 1) := by
      rw [add_mul, sub_mul (a / x), e]; ring
    have h2 : (x - a) * (x - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    by_contra hc
    have : 0 < ((x - a) + (a / x - 1)) * x := mul_pos (lt_of_not_ge hc) hx0
    linarith
  linarith

/-- x − 2 log (x/2) is monotone on [2, ∞). -/
theorem g_mono {b x : ℝ} (hx : 2 ≤ x) (hxb : x ≤ b) : x - 2 * Real.log (x / 2) ≤ b - 2 * Real.log (b / 2) := by
  have hx0 : 0 < x := by linarith
  have hb0 : 0 < b := by linarith
  have h := Real.log_le_sub_one_of_pos (show 0 < b / x by positivity)
  have e2 : Real.log (b / x) = Real.log (b / 2) - Real.log (x / 2) := by
    rw [← Real.log_div (by positivity) (by positivity)]; congr 1; field_simp
  rw [e2] at h
  have e : b / x * x = b := by field_simp
  have k : (x - b) + 2 * (b / x - 1) ≤ 0 := by
    have m : ((x - b) + 2 * (b / x - 1)) * x = (x - b) * (x - 2) := by
      rw [add_mul, mul_assoc, sub_mul (b / x), e]; ring
    have h2 : (x - b) * (x - 2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    by_contra hc
    have : 0 < ((x - b) + 2 * (b / x - 1)) * x := mul_pos (lt_of_not_ge hc) hx0
    linarith
  linarith

/-- On the sublevel set of Volterra's function through the certified state at the end radius of the
cells, u v³ is bounded above. -/
theorem uv_upper {u v u0 v0 : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hu0 : 9804262057 / 10000000000 ≤ u0) (hu0' : u0 ≤ 1)
    (hv0 : 2 ≤ v0) (hv0' : v0 ≤ 20328598293 / 10000000000)
    (hV : u + v - Real.log u - 2 * Real.log (v / 2) ≤
      u0 + v0 - Real.log u0 - 2 * Real.log (v0 / 2)) :
    u * v ^ 3 < 865 / 100 := by
  have fu := f_anti (show (0 : ℝ) < 9804262057 / 10000000000 by norm_num) hu0 hu0'
  have fv := g_mono hv0 hv0'
  have hy : 0 < v / 2 := by positivity
  have d1 := Checked.Math.BEHTail.dual' hu (show (-1 : ℝ) < 1 / 80 by norm_num)
  have d2 := Checked.Math.BEHTail.dual' hy (show (-1 : ℝ) < 3 / 160 by norm_num)
  norm_num at d1 d2
  have hprod : Real.log (u * v ^ 3 / 8) = Real.log u + 3 * Real.log (v / 2) := by
    have : u * v ^ 3 / 8 = u * (v / 2) ^ 3 := by ring
    rw [this, Real.log_mul hu.ne' (by positivity), Real.log_pow]
    push_cast; ring
  have l81 := log_81
  have l163 := log_163
  have lu := log_ul
  have lv : 162963 / 10000000 ≤ Real.log ((20328598293 / 10000000000 : ℝ) / 2) := by
    have : (20328598293 / 10000000000 : ℝ) / 2 = 20328598293 / 20000000000 := by norm_num
    rw [this]; exact log_vh
  have lX := log_X
  have key : Real.log (u * v ^ 3 / 8) < Real.log (865 / 800) := by
    rw [hprod]; linarith
  have h8 := (Real.log_lt_log_iff (by positivity) (by norm_num)).1 key
  linarith

end Work.Math.BEH2Tail
