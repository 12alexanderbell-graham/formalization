import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases

/-! Thomas–Fermi, `TFExBase`: the clamped field of the regular system of u = y(t²) and Φ = y'(t²) in t = √x (the power of u extended by zero below zero). Promoted from `Work/Math/TFExBase.lean`. -/

namespace Checked.Math.TFExBase
open Set

/-- `v^{3/2}` for `v ≥ 0`, extended by `0` below. -/
noncomputable def g (v : ℝ) : ℝ := max v 0 * Real.sqrt (max v 0)

/-- Clamp of `y` to `[−c, c]`. -/
noncomputable def cl (c y : ℝ) : ℝ := max (-c) (min c y)

/-- The clamped field in the state `p = (u, Φ)`. -/
noncomputable def F (T t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (2 * min (max t 0) T * cl 10 p.2, 2 * g (min p.1 2))

theorem F_fst {T t : ℝ} (ht : t ∈ Icc 0 T) (p : ℝ × ℝ) : (F T t p).1 = 2 * t * cl 10 p.2 := by
  simp [F, max_eq_left ht.1, min_eq_left ht.2]

theorem F_snd (T t : ℝ) (p : ℝ × ℝ) : (F T t p).2 = 2 * g (min p.1 2) := rfl

theorem g_of_nonpos {v : ℝ} (h : v ≤ 0) : g v = 0 := by simp [g, max_eq_right h]

theorem g_nonneg (v : ℝ) : 0 ≤ g v := mul_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)

theorem g_pos {v : ℝ} (h : 0 < v) : 0 < g v := by
  simp only [g, max_eq_left h.le]; exact mul_pos h (Real.sqrt_pos.2 h)

theorem g_eq_rpow {v : ℝ} (h : 0 ≤ v) : g v = v ^ ((3 : ℝ) / 2) := by
  simp only [g, max_eq_left h]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' h (by norm_num)]; norm_num

theorem cl_of_abs_le {c y : ℝ} (h : |y| ≤ c) : cl c y = y := by
  unfold cl; rw [abs_le] at h; rw [min_eq_right h.2, max_eq_right h.1]

theorem cl_pos_iff {y : ℝ} : 0 < cl 10 y ↔ 0 < y := by
  unfold cl; constructor
  · intro h; by_contra h'; push Not at h'
    have : min 10 y ≤ 0 := min_le_of_right_le h'
    have : max (-10) (min 10 y) ≤ 0 := max_le (by norm_num) this
    linarith
  · intro h; exact lt_max_of_lt_right (lt_min (by norm_num) h)

theorem cl_neg_iff {y : ℝ} : cl 10 y < 0 ↔ y < 0 := by
  unfold cl; constructor
  · intro h; by_contra h'; push Not at h'
    have : 0 ≤ min 10 y := le_min (by norm_num) h'
    linarith [le_max_right (-10 : ℝ) (min 10 y)]
  · intro h; exact max_lt (by norm_num) (min_lt_of_right_lt h)

theorem cl_eq_zero_iff {y : ℝ} : cl 10 y = 0 ↔ y = 0 := by
  constructor
  · intro h
    rcases lt_trichotomy y 0 with hy | hy | hy
    · linarith [cl_neg_iff.2 hy]
    · exact hy
    · linarith [cl_pos_iff.2 hy]
  · rintro rfl; simp [cl]

end Checked.Math.TFExBase
