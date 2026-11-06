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
import Checked.Math.TFExBase

/-! Thomas–Fermi, `TFExFlow`: Picard–Lindelöf flow of the clamped field, continuous in the initial slope; consistency of flows and backward uniqueness. Promoted from `Work/Math/TFExFlow.lean`. -/

namespace Checked.Math.TFExFlow
open Set Checked.Math.TFExBase Topology

theorem cl_sub (c y z : ℝ) : |cl c y - cl c z| ≤ |y - z| := by
  unfold cl
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp) ?_)
  exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by simp) le_rfl)

theorem abs_cl_le (y : ℝ) : |cl 10 y| ≤ 10 := by
  unfold cl; rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem key (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hx2 : x ^ 2 ≤ 2) (hy2 : y ^ 2 ≤ 2) :
    |x ^ 2 * x - y ^ 2 * y| ≤ 3 * |x ^ 2 - y ^ 2| := by
  have e1 : x ^ 2 * x - y ^ 2 * y = (x - y) * (x ^ 2 + x * y + y ^ 2) := by ring
  have e2 : x ^ 2 - y ^ 2 = (x - y) * (x + y) := by ring
  have hx3 : x ≤ 3 / 2 := by nlinarith
  have hy3 : y ≤ 3 / 2 := by nlinarith
  rw [e1, e2, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ x ^ 2 + x * y + y ^ 2),
    abs_of_nonneg (by positivity : 0 ≤ x + y)]
  have : x ^ 2 + x * y + y ^ 2 ≤ 3 * (x + y) := by nlinarith [sq_nonneg (x - y)]
  nlinarith [abs_nonneg (x - y)]

theorem g_min_eq (a : ℝ) :
    g (min a 2) = Real.sqrt (max (min a 2) 0) ^ 2 * Real.sqrt (max (min a 2) 0) := by
  rw [Real.sq_sqrt (le_max_right _ _)]; rfl

theorem g_lip (a b : ℝ) : |g (min a 2) - g (min b 2)| ≤ 3 * |a - b| := by
  rw [g_min_eq, g_min_eq]
  set a' := max (min a 2) 0
  set b' := max (min b 2) 0
  have ha0 : 0 ≤ a' := le_max_right _ _
  have hb0 : 0 ≤ b' := le_max_right _ _
  have ha2 : a' ≤ 2 := max_le (min_le_right _ _) (by norm_num)
  have hb2 : b' ≤ 2 := max_le (min_le_right _ _) (by norm_num)
  have h := key (Real.sqrt a') (Real.sqrt b') (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (by rw [Real.sq_sqrt ha0]; exact ha2) (by rw [Real.sq_sqrt hb0]; exact hb2)
  rw [Real.sq_sqrt ha0, Real.sq_sqrt hb0] at h
  have hab : |a' - b'| ≤ |a - b| := by
    refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ (by simp))
    exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le le_rfl (by simp))
  rw [Real.sq_sqrt ha0, Real.sq_sqrt hb0]
  linarith

theorem g_min_le (a : ℝ) : g (min a 2) ≤ 3 := by
  have : g (min a 2) ≤ g 2 := by
    unfold g
    have h1 : max (min a 2) 0 ≤ max 2 0 := max_le_max (min_le_right _ _) le_rfl
    exact mul_le_mul h1 (Real.sqrt_le_sqrt h1) (Real.sqrt_nonneg _) (le_max_right _ _)
  have h2 : g 2 ≤ 3 := by
    have e : g 2 = 2 * Real.sqrt 2 := by simp [g]
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hs0 := Real.sqrt_nonneg 2
    rw [e]; nlinarith
  linarith

theorem lipschitz_F (T : ℝ) (hT : 0 ≤ T) (t : ℝ) :
    LipschitzWith (Real.toNNReal (2 * T + 10)) (F T t) := by
  have hK : (0 : ℝ) ≤ 2 * T + 10 := by linarith
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  rw [Real.coe_toNNReal _ hK]
  simp only [F, Prod.dist_eq, Real.dist_eq]
  have hd1 : |p.1 - q.1| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_left _ _
  have hd2 : |p.2 - q.2| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_right _ _
  have hm0 : 0 ≤ max |p.1 - q.1| |p.2 - q.2| := (abs_nonneg _).trans hd1
  have htc0 : 0 ≤ min (max t 0) T := le_min (le_max_right _ _) hT
  have htcT : min (max t 0) T ≤ T := min_le_right _ _
  refine max_le ?_ ?_
  · have e : 2 * min (max t 0) T * cl 10 p.2 - 2 * min (max t 0) T * cl 10 q.2 =
        2 * min (max t 0) T * (cl 10 p.2 - cl 10 q.2) := by ring
    rw [e, abs_mul, abs_of_nonneg (by positivity)]
    have := cl_sub 10 p.2 q.2
    calc 2 * min (max t 0) T * |cl 10 p.2 - cl 10 q.2|
        ≤ 2 * T * max |p.1 - q.1| |p.2 - q.2| :=
          mul_le_mul (by linarith) (this.trans hd2) (abs_nonneg _) (by linarith)
      _ ≤ (2 * T + 10) * max |p.1 - q.1| |p.2 - q.2| := by nlinarith
  · have e : 2 * g (min p.1 2) - 2 * g (min q.1 2) = 2 * (g (min p.1 2) - g (min q.1 2)) := by
      ring
    rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have := g_lip p.1 q.1
    nlinarith

theorem norm_F_le (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (p : ℝ × ℝ) : ‖F T t p‖ ≤ 20 * T + 10 := by
  simp only [F, Prod.norm_def, Real.norm_eq_abs]
  have htc0 : 0 ≤ min (max t 0) T := le_min (le_max_right _ _) hT
  have htcT : min (max t 0) T ≤ T := min_le_right _ _
  refine max_le ?_ ?_
  · rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2),
      abs_of_nonneg htc0]
    have := abs_cl_le p.2
    nlinarith [abs_nonneg (cl 10 p.2)]
  · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2), abs_of_nonneg (g_nonneg _)]
    have := g_min_le p.1
    linarith

theorem continuous_F (T : ℝ) (p : ℝ × ℝ) : Continuous (fun t => F T t p) := by
  unfold F
  refine Continuous.prodMk ?_ continuous_const
  exact ((continuous_const.mul ((continuous_id.max continuous_const).min continuous_const)).mul
    continuous_const)

theorem exists_flow (T : ℝ) (hT : 0 < T) : ∃ α : ℝ → ℝ → ℝ × ℝ,
    (∀ s ∈ Icc (-10 : ℝ) 0, α s 0 = (1, s) ∧
      ∀ t ∈ Icc 0 T, HasDerivWithinAt (α s) (F T t (α s t)) (Icc 0 T) t) ∧
    (∀ t ∈ Icc 0 T, ContinuousOn (fun s => α s t) (Icc (-10 : ℝ) 0)) := by
  set L : ℝ := 20 * T + 10 with hL
  have hL0 : 0 ≤ L := by positivity
  have hPL : IsPicardLindelof (F T) (tmin := 0) (tmax := T)
      ⟨0, le_rfl, hT.le⟩ ((1 : ℝ), (0 : ℝ)) (Real.toNNReal (10 + L * T)) (Real.toNNReal 10)
      (Real.toNNReal L) (Real.toNNReal (2 * T + 10)) :=
    { lipschitzOnWith := fun t _ => (lipschitz_F T hT.le t).lipschitzOnWith
      continuousOn := fun x _ => (continuous_F T x).continuousOn
      norm_le := fun t _ p _ => by
        rw [Real.coe_toNNReal _ hL0]; exact norm_F_le T hT.le t p
      mul_max_le := by
        rw [Real.coe_toNNReal _ hL0, Real.coe_toNNReal _ (by positivity),
          Real.coe_toNNReal _ (by norm_num)]
        simp only
        rw [sub_self, sub_zero, max_eq_left hT.le]
        linarith }
  obtain ⟨α, hα, L', hlip⟩ := hPL.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  have hmem : ∀ s ∈ Icc (-10 : ℝ) 0,
      ((1 : ℝ), s) ∈ Metric.closedBall ((1 : ℝ), (0 : ℝ)) (Real.toNNReal 10 : ℝ) := by
    intro s hs
    rw [Metric.mem_closedBall, Prod.dist_eq, Real.coe_toNNReal _ (by norm_num)]
    simp only [dist_self, Real.dist_eq, sub_zero]
    refine max_le (by norm_num) ?_
    rw [abs_le]; exact ⟨hs.1, by linarith [hs.2]⟩
  refine ⟨fun s => α ((1 : ℝ), s), fun s hs => ?_, fun t ht => ?_⟩
  · exact hα _ (hmem s hs)
  · have hc := (hlip t ht).continuousOn
    refine hc.comp (continuous_const.prodMk continuous_id).continuousOn ?_
    intro s hs; exact hmem s hs

theorem F_eq {T T' t : ℝ} (ht : t ∈ Icc 0 T) (hTT' : T ≤ T') (p : ℝ × ℝ) :
    F T t p = F T' t p := by
  simp only [F, max_eq_left ht.1, min_eq_left ht.2, min_eq_left (ht.2.trans hTT')]

/-- two solutions, of F T on [0,T] and of F T' on [0,T'] (T ≤ T'), with the same start agree on [0,T] -/
theorem consistent {T T' : ℝ} (hT : 0 < T) (hTT' : T ≤ T') (f g : ℝ → ℝ × ℝ) (h0 : f 0 = g 0)
    (hf : ∀ t ∈ Icc 0 T, HasDerivWithinAt f (F T t (f t)) (Icc 0 T) t)
    (hg : ∀ t ∈ Icc 0 T', HasDerivWithinAt g (F T' t (g t)) (Icc 0 T') t) :
    EqOn f g (Icc 0 T) := by
  have hT' : 0 ≤ T' := hT.le.trans hTT'
  refine ODE_solution_unique_of_mem_Icc_right (v := F T') (s := fun _ => univ)
    (K := Real.toNNReal (2 * T' + 10))
    (fun t _ => (lipschitz_F T' hT' t).lipschitzOnWith)
    (fun t ht => (hf t ht).continuousWithinAt) (fun t ht => ?_) (fun _ _ => mem_univ _)
    (fun t ht => ((hg t ⟨ht.1, ht.2.trans hTT'⟩).continuousWithinAt.mono
      (Icc_subset_Icc_right hTT'))) (fun t ht => ?_) (fun _ _ => mem_univ _) h0
  · have hmem : t ∈ Icc 0 T := ⟨ht.1, ht.2.le⟩
    rw [← F_eq hmem hTT']
    refine (hf t hmem).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)
  · have hmem : t ∈ Icc 0 T' := ⟨ht.1, ht.2.le.trans hTT'⟩
    refine (hg t hmem).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (Icc_mem_nhdsGE (lt_of_lt_of_le ht.2 hTT'))
      (Icc_subset_Icc_left ht.1)

/-- backward uniqueness against the zero solution -/
theorem zero_backward {T t₀ : ℝ} (hT : 0 < T) (ht₀ : t₀ ∈ Ioc 0 T) (f : ℝ → ℝ × ℝ)
    (hf : ∀ t ∈ Icc 0 T, HasDerivWithinAt f (F T t (f t)) (Icc 0 T) t) (h0 : f t₀ = 0) :
    f 0 = 0 := by
  have hF0 : ∀ t, F T t 0 = 0 := by
    intro t
    have hc : cl 10 0 = 0 := cl_eq_zero_iff.2 rfl
    have hg : g (min 0 2) = 0 := g_of_nonpos (by norm_num)
    simp only [F, Prod.snd_zero, Prod.fst_zero, hc, hg, mul_zero]; rfl
  have h := ODE_solution_unique_of_mem_Icc_left (v := F T) (s := fun _ => univ)
    (K := Real.toNNReal (2 * T + 10)) (a := 0) (b := t₀) (f := f) (g := fun _ => 0)
    (fun t _ => (lipschitz_F T hT.le t).lipschitzOnWith)
    (fun t ht => (hf t ⟨ht.1, ht.2.trans ht₀.2⟩).continuousWithinAt.mono
      (Icc_subset_Icc_right ht₀.2))
    (fun t ht => ?_) (fun _ _ => mem_univ _) continuousOn_const
    (fun t _ => by rw [hF0]; exact hasDerivWithinAt_const _ _ _) (fun _ _ => mem_univ _) h0
  · exact h ⟨le_rfl, ht₀.1.le⟩
  · have hmem : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.trans ht₀.2⟩
    refine (hf t hmem).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (Icc_mem_nhdsLE ht.1) (Icc_subset_Icc_right hmem.2)

end Checked.Math.TFExFlow
