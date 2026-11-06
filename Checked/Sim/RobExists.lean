import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Bound

/-!
# Robertson's network: existence for the clamped reduced field

The reduced Robertson field (y₁ = 1 − y₂ − y₃ eliminated) with its arguments clamped to the box
|y₂| ≤ 1/1000, −1/10 ≤ y₃ ≤ 11/10 is globally Lipschitz and bounded on ℝ × ℝ (sup norm), so
Picard–Lindelöf gives a solution on [0, 40] from (0, 0). On the box the clamped field equals
the true one; the certified enclosure shows that the solution never leaves the box.
-/

namespace Checked.Sim.RobExists
open Set

/-- Clamp of `y` to [lo, hi]. -/
noncomputable def cl (lo hi y : ℝ) : ℝ := max lo (min hi y)

theorem cl_sub (lo hi y z : ℝ) : |cl lo hi y - cl lo hi z| ≤ |y - z| := by
  unfold cl
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp) ?_)
  exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by simp) le_rfl)

theorem cl_mem {lo hi : ℝ} (h : lo ≤ hi) (y : ℝ) : lo ≤ cl lo hi y ∧ cl lo hi y ≤ hi := by
  unfold cl
  exact ⟨le_max_left _ _, max_le h (min_le_left _ _)⟩

theorem cl_of_mem {lo hi y : ℝ} (h1 : lo ≤ y) (h2 : y ≤ hi) : cl lo hi y = y := by
  unfold cl; rw [min_eq_right h2, max_eq_right h1]

/-- Clamped reduced Robertson field on ℝ × ℝ (sup norm), box |y₂| ≤ 1/1000,
−1/10 ≤ y₃ ≤ 11/10. -/
noncomputable def Φc (p : ℝ × ℝ) : ℝ × ℝ :=
  (1 / 25 * (1 - cl (-1/1000) (1/1000) p.1 - cl (-1/10) (11/10) p.2)
      - 10000 * cl (-1/1000) (1/1000) p.1 * cl (-1/10) (11/10) p.2
      - 30000000 * cl (-1/1000) (1/1000) p.1 ^ 2,
   30000000 * cl (-1/1000) (1/1000) p.1 ^ 2)

theorem comb {a b x y A B m : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hx : |x| ≤ m) (hy : |y| ≤ m) :
    |a * x + b * y| ≤ (A + B) * m := by
  calc |a * x + b * y| ≤ |a * x| + |b * y| := abs_add_le _ _
    _ = |a| * |x| + |b| * |y| := by rw [abs_mul, abs_mul]
    _ ≤ A * m + B * m := add_le_add
        (mul_le_mul ha hx (abs_nonneg _) ((abs_nonneg _).trans ha))
        (mul_le_mul hb hy (abs_nonneg _) ((abs_nonneg _).trans hb))
    _ = (A + B) * m := by ring

theorem u_mem (y : ℝ) : -1 / 1000 ≤ cl (-1/1000) (1/1000) y ∧ cl (-1/1000) (1/1000) y ≤ 1 / 1000 :=
  cl_mem (by norm_num) y

theorem v_mem (y : ℝ) : -1 / 10 ≤ cl (-1/10) (11/10) y ∧ cl (-1/10) (11/10) y ≤ 11 / 10 :=
  cl_mem (by norm_num) y

theorem lipΦc : LipschitzWith ⟨80000, by norm_num⟩ Φc := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  simp only [Φc, Prod.dist_eq, Real.dist_eq]
  change _ ≤ (80000 : ℝ) * _
  set m := max |p.1 - q.1| |p.2 - q.2|
  have hu := (cl_sub (-1/1000) (1/1000) p.1 q.1).trans (le_max_left _ _ : |p.1 - q.1| ≤ m)
  have hv := (cl_sub (-1/10) (11/10) p.2 q.2).trans (le_max_right _ _ : |p.2 - q.2| ≤ m)
  have hm : 0 ≤ m := (abs_nonneg _).trans (le_max_left _ _)
  obtain ⟨u1, u2⟩ := u_mem p.1
  obtain ⟨u1', u2'⟩ := u_mem q.1
  obtain ⟨v1, v2⟩ := v_mem p.2
  generalize cl (-1/1000) (1/1000) p.1 = u at *
  generalize cl (-1/1000) (1/1000) q.1 = u' at *
  generalize cl (-1/10) (11/10) p.2 = v at *
  generalize cl (-1/10) (11/10) q.2 = v' at *
  refine max_le ?_ ?_
  · have e : (1 / 25 * (1 - u - v) - 10000 * u * v - 30000000 * u ^ 2) -
        (1 / 25 * (1 - u' - v') - 10000 * u' * v' - 30000000 * u' ^ 2) =
        (-(1 / 25) - 10000 * v - 30000000 * (u + u')) * (u - u') +
          (-(1 / 25) - 10000 * u') * (v - v') := by ring
    rw [e]
    have h1 : |-(1 / 25) - 10000 * v - 30000000 * (u + u')| ≤ 71001 := by
      rw [abs_le]; constructor <;> linarith
    have h2 : |-(1 / 25) - 10000 * u'| ≤ 11 := by
      rw [abs_le]; constructor <;> linarith
    have := comb h1 h2 hu hv
    linarith
  · have e : 30000000 * u ^ 2 - 30000000 * u' ^ 2 =
        (30000000 * (u + u')) * (u - u') + 0 * (v - v') := by ring
    rw [e]
    have h1 : |30000000 * (u + u')| ≤ 60000 := by
      rw [abs_le]; constructor <;> linarith
    have h2 : |(0 : ℝ)| ≤ 0 := by simp
    have := comb h1 h2 hu hv
    linarith

theorem normΦc (p : ℝ × ℝ) : ‖Φc p‖ ≤ 50 := by
  obtain ⟨u1, u2⟩ := u_mem p.1
  obtain ⟨v1, v2⟩ := v_mem p.2
  simp only [Φc, Prod.norm_def, Real.norm_eq_abs]
  generalize cl (-1/1000) (1/1000) p.1 = u at *
  generalize cl (-1/10) (11/10) p.2 = v at *
  have hu2 : u ^ 2 ≤ 1 / 1000000 := by nlinarith
  have hu0 : 0 ≤ u ^ 2 := sq_nonneg u
  have huv1 : u * v ≤ 11 / 10000 := by nlinarith
  have huv2 : -(11 / 10000) ≤ u * v := by nlinarith
  refine max_le ?_ ?_ <;> rw [abs_le] <;> constructor <;> nlinarith

theorem exists_clamped : ∃ α : ℝ → ℝ × ℝ, α 0 = (0, 0) ∧
    ∀ t ∈ Icc (0 : ℝ) 40, HasDerivWithinAt α (Φc (α t)) (Icc 0 40) t := by
  have hPL : IsPicardLindelof (fun _ => Φc) (tmin := 0) (tmax := 40)
      ⟨0, by norm_num, by norm_num⟩ ((0 : ℝ), (0 : ℝ)) 2000 0 50 ⟨80000, by norm_num⟩ :=
    { lipschitzOnWith := fun _ _ => lipΦc.lipschitzOnWith
      continuousOn := fun _ _ => continuousOn_const
      norm_le := fun _ _ p _ => by
        have := normΦc p; exact_mod_cast this
      mul_max_le := by
        simp only [NNReal.coe_ofNat, NNReal.coe_zero, sub_zero]
        norm_num }
  obtain ⟨α, h0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, h0, hα⟩

end Checked.Sim.RobExists
