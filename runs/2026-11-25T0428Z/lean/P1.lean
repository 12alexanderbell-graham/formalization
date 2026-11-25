import Checked.Math.BEFocus
import Checked.Math.GelfandExtremaMain
import Checked.Math.BEAllMain
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

namespace GTR
open Set Filter Topology
open Checked.Math.BEOCell (Nw)
open Checked.Math.BEFocus

theorem abs_x_le (x y : ℝ) : |x| ≤ Real.sqrt (Nw x y) := Real.abs_le_sqrt (x_sq_le_Nw x y)

/-- The angular momentum is a quarter of `Nw` up to a cubic term. -/
theorem Lq_err (x y : ℝ) : |Lq x y - Nw x y / 4| ≤ 3 * Nw x y * Real.sqrt (Nw x y) := by
  have e : Lq x y - Nw x y / 4 = x * y * (2 * x + y) := by unfold Lq Nw; ring
  rw [e]
  have hx := abs_x_le x y
  have hy := y_abs_le x y
  have hr := Real.sqrt_nonneg (Nw x y)
  have hN : Real.sqrt (Nw x y) ^ 2 = Nw x y := Real.sq_sqrt (Checked.Math.BEOCell.Nw_nonneg x y)
  have h3 : |2 * x + y| ≤ 3 * Real.sqrt (Nw x y) := by
    calc |2 * x + y| ≤ |2 * x| + |y| := abs_add_le _ _
      _ = 2 * |x| + |y| := by rw [abs_mul, abs_two]
      _ ≤ 3 * Real.sqrt (Nw x y) := by linarith
  rw [abs_mul, abs_mul]
  calc |x| * |y| * |2 * x + y| ≤ Real.sqrt (Nw x y) * Real.sqrt (Nw x y) * (3 * Real.sqrt (Nw x y)) := by
        apply mul_le_mul (mul_le_mul hx hy (abs_nonneg _) hr) h3 (abs_nonneg _) (by positivity)
    _ = 3 * Nw x y * Real.sqrt (Nw x y) := by linear_combination 3 * Real.sqrt (Nw x y) * hN

/-- `Dq` is `-Nw` up to a cubic term. -/
theorem Dq_err (x y : ℝ) : |Dq x y + Nw x y| ≤ 36 * Nw x y * Real.sqrt (Nw x y) := by
  have e : Dq x y + Nw x y = -(4 * x) * (4 * x ^ 2 + 4 * x * y - y ^ 2) := by unfold Dq; ring
  rw [e]
  have hx := abs_x_le x y
  have hy := y_abs_le x y
  have hr := Real.sqrt_nonneg (Nw x y)
  have hN : Real.sqrt (Nw x y) ^ 2 = Nw x y := Real.sq_sqrt (Checked.Math.BEOCell.Nw_nonneg x y)
  have hxx : x ^ 2 ≤ Nw x y := x_sq_le_Nw x y
  have hyy : y ^ 2 ≤ Nw x y := by
    have := sq_abs y ▸ pow_le_pow_left₀ (abs_nonneg y) hy 2; linarith
  have hxy : |x * y| ≤ Nw x y := by
    rw [abs_mul]
    have := mul_le_mul hx hy (abs_nonneg _) hr
    nlinarith
  have h9 : |4 * x ^ 2 + 4 * x * y - y ^ 2| ≤ 9 * Nw x y := by
    have a1 := abs_le.1 hxy
    rw [abs_le]; constructor <;> nlinarith
  rw [abs_mul, abs_neg, abs_mul, show |(4 : ℝ)| = 4 by norm_num]
  calc 4 * |x| * |4 * x ^ 2 + 4 * x * y - y ^ 2| ≤ 4 * Real.sqrt (Nw x y) * (9 * Nw x y) := by
        apply mul_le_mul (by linarith) h9 (abs_nonneg _) (by positivity)
    _ = 36 * Nw x y * Real.sqrt (Nw x y) := by ring

end GTR
