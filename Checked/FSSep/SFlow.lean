import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Order.IntermediateValue
import Checked.FSSep.SBase

/-! Falkner–Skan separation, a global flow of the clamped adverse-sign field from a zero wall value, continuous in the coefficient, with forward and backward uniqueness. Module `SFlow`, promoted from `Work/FSSep/SFlow.lean`. -/

namespace Checked.FSSep.SFlow
open Set Checked.FSNeg.NBase Checked.FSSep.SBase
theorem cl_sub (c y z : ℝ) : |cl c y - cl c z| ≤ |y - z| := by
  unfold cl
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp) ?_)
  exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by simp) le_rfl)

theorem abs_cl_le {c : ℝ} (hc : 0 ≤ c) (y : ℝ) : |cl c y| ≤ c := by
  unfold cl; rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem lip (K : ℝ) {T t : ℝ} (ht : t ∈ Icc 0 T) :
    LipschitzWith (Real.toNNReal (|K| * T + 4 * |K| + 4)) (vS K t) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  have hK0 : 0 ≤ |K| := abs_nonneg K
  rw [Real.coe_toNNReal _ (by positivity)]
  simp only [vS, Prod.dist_eq, Real.dist_eq]
  set m := max |y.1 - z.1| (max |y.2.1 - z.2.1| |y.2.2 - z.2.2|)
  have hd1 : |y.1 - z.1| ≤ m := le_max_left _ _
  have hd2 : |y.2.1 - z.2.1| ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hd3 : |y.2.2 - z.2.2| ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  have hm : 0 ≤ m := (abs_nonneg _).trans hd1
  set C := max t 0 + 2 with hC
  have hC0 : 0 ≤ C := by positivity
  have hCT : C ≤ T + 2 := by
    have : max t 0 ≤ T := max_le ht.2 hT
    linarith
  refine max_le ?_ (max_le ?_ ?_)
  · have := cl_sub 2 y.2.1 z.2.1; nlinarith [mul_nonneg hK0 hT, mul_nonneg (mul_nonneg hK0 hT) hm, mul_nonneg hK0 hm]
  · have := cl_sub 2 y.2.2 z.2.2; nlinarith [mul_nonneg hK0 hT, mul_nonneg (mul_nonneg hK0 hT) hm, mul_nonneg hK0 hm]
  · set a := cl C y.1
    set a' := cl C z.1
    set b := cl 2 y.2.2
    set b' := cl 2 z.2.2
    set c := cl 2 y.2.1
    set c' := cl 2 z.2.1
    have ha : |a - a'| ≤ |y.1 - z.1| := cl_sub C y.1 z.1
    have hb : |b - b'| ≤ |y.2.2 - z.2.2| := cl_sub 2 y.2.2 z.2.2
    have hc : |c - c'| ≤ |y.2.1 - z.2.1| := cl_sub 2 y.2.1 z.2.1
    have hbb : |b| ≤ 2 := abs_cl_le (by norm_num) _
    have haa : |a'| ≤ C := abs_cl_le hC0 _
    have hcc : |c| ≤ 2 := abs_cl_le (by norm_num) _
    have hcc' : |c'| ≤ 2 := abs_cl_le (by norm_num) _
    have e : -(K * a * b) + 1 - c ^ 2 - (-(K * a' * b') + 1 - c' ^ 2)
        = -(K * ((a - a') * b + a' * (b - b'))) + (c + c') * (c' - c) := by ring
    rw [abs_sub_comm] at hc
    rw [e]
    have h1 : |(a - a') * b| ≤ 2 * m := by
      rw [abs_mul, mul_comm]
      exact mul_le_mul hbb (ha.trans hd1) (abs_nonneg _) (by norm_num)
    have h2 : |a' * (b - b')| ≤ C * m := by
      rw [abs_mul]
      exact mul_le_mul haa (hb.trans hd3) (abs_nonneg _) hC0
    have h4 : |(c + c') * (c' - c)| ≤ 4 * m := by
      rw [abs_mul]
      have : |c + c'| ≤ 4 := (abs_add_le c c').trans (by linarith)
      exact mul_le_mul this (hc.trans hd2) (abs_nonneg _) (by norm_num)
    have h3 := abs_add_le ((a - a') * b) (a' * (b - b'))
    have h5 := abs_add_le (-(K * ((a - a') * b + a' * (b - b')))) ((c + c') * (c' - c))
    rw [abs_neg, abs_mul] at h5
    have h6 : |(a - a') * b + a' * (b - b')| ≤ (T + 4) * m := by nlinarith
    have h7 : |K| * |(a - a') * b + a' * (b - b')| ≤ |K| * ((T + 4) * m) :=
      mul_le_mul_of_nonneg_left h6 hK0
    nlinarith [mul_nonneg hK0 hm]

theorem norm_le (K : ℝ) {T t : ℝ} (ht : t ∈ Icc 0 T) (y : ℝ × ℝ × ℝ) : ‖vS K t y‖ ≤ 2 * |K| * T + 4 * |K| + 5 := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  simp only [vS, Prod.norm_def, Real.norm_eq_abs]
  set C := max t 0 + 2 with hC
  have hC0 : 0 ≤ C := by positivity
  have hCT : C ≤ T + 2 := by
    have : max t 0 ≤ T := max_le ht.2 hT
    linarith
  have h1 := abs_cl_le (by norm_num : (0 : ℝ) ≤ 2) y.2.1
  have h2 := abs_cl_le (by norm_num : (0 : ℝ) ≤ 2) y.2.2
  have h3 := abs_cl_le hC0 y.1
  have hK0 : 0 ≤ |K| := abs_nonneg K
  have hKT : 0 ≤ |K| * T := mul_nonneg hK0 hT
  refine max_le (by linarith) (max_le (by linarith) ?_)
  have hab : |K * cl C y.1 * cl 2 y.2.2| ≤ |K| * (C * 2) := by
    rw [abs_mul, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul h3 h2 (abs_nonneg _) hC0) hK0
  have hab2 : |K| * (C * 2) ≤ |K| * ((T + 2) * 2) := mul_le_mul_of_nonneg_left (by linarith) hK0
  have hsq : |cl 2 y.2.1 ^ 2| ≤ 4 := by
    rw [abs_pow]; nlinarith [abs_nonneg (cl 2 y.2.1)]
  have k1 := abs_sub (-(K * cl C y.1 * cl 2 y.2.2) + 1) (cl 2 y.2.1 ^ 2)
  have k2 := abs_add_le (-(K * cl C y.1 * cl 2 y.2.2)) 1
  rw [abs_neg] at k2
  simp only [abs_one] at k2
  linarith

theorem cont (K : ℝ) (y : ℝ × ℝ × ℝ) : Continuous (fun t => vS K t y) := by
  unfold vS cl
  fun_prop

/-- A solution on [0, T] for every T > 0. -/
theorem local_sol (K T : ℝ) (hT : 0 < T) : ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = (0, 0, 0) ∧
    ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vS K t (Y t)) (Icc 0 T) t := by
  set L : ℝ := 2 * |K| * T + 4 * |K| + 5 with hL
  have hL0 : 0 ≤ L := by positivity
  have hPL : IsPicardLindelof (vS K) (tmin := 0) (tmax := T) ⟨0, le_rfl, hT.le⟩
      ((0 : ℝ), (0 : ℝ), (0 : ℝ)) (Real.toNNReal (L * T)) 0 (Real.toNNReal L)
      (Real.toNNReal (|K| * T + 4 * |K| + 4)) :=
    { lipschitzOnWith := fun t ht => (lip K ht).lipschitzOnWith
      continuousOn := fun x _ => (cont K x).continuousOn
      norm_le := fun t ht p _ => by
        rw [Real.coe_toNNReal _ hL0]; exact norm_le K ht p
      mul_max_le := by
        rw [Real.coe_toNNReal _ hL0, Real.coe_toNNReal _ (by positivity)]
        simp only [NNReal.coe_zero, sub_zero, sub_self]
        rw [max_eq_left hT.le] }
  exact hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- Forward uniqueness on [0, T]. -/
theorem unique_right {K T : ℝ} (hT : 0 ≤ T) {Y Z : ℝ → ℝ × ℝ × ℝ}
    (hY : ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vS K t (Y t)) (Icc 0 T) t)
    (hZ : ∀ t ∈ Icc 0 T, HasDerivWithinAt Z (vS K t (Z t)) (Icc 0 T) t)
    (h0 : Y 0 = Z 0) : EqOn Y Z (Icc 0 T) := by
  refine ODE_solution_unique_of_mem_Icc_right (v := vS K) (s := fun _ => univ)
    (K := Real.toNNReal (|K| * T + 4 * |K| + 4))
    (fun t ht => (lip K (Ico_subset_Icc_self ht)).lipschitzOnWith)
    (fun t ht => (hY t ht).continuousWithinAt) (fun t ht => ?_) (fun _ _ => mem_univ _)
    (fun t ht => (hZ t ht).continuousWithinAt) (fun t ht => ?_) (fun _ _ => mem_univ _) h0
  · have hmem : t ∈ Icc 0 T := ⟨ht.1, ht.2.le⟩
    refine (hY t hmem).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)
  · have hmem : t ∈ Icc 0 T := ⟨ht.1, ht.2.le⟩
    refine (hZ t hmem).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)

/-- Backward uniqueness on [0, T]. -/
theorem unique_left {K T : ℝ} (hT : 0 ≤ T) {Y Z : ℝ → ℝ × ℝ × ℝ}
    (hY : ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vS K t (Y t)) (Icc 0 T) t)
    (hZ : ∀ t ∈ Icc 0 T, HasDerivWithinAt Z (vS K t (Z t)) (Icc 0 T) t)
    (hT' : Y T = Z T) : EqOn Y Z (Icc 0 T) := by
  refine ODE_solution_unique_of_mem_Icc_left (v := vS K) (s := fun _ => univ)
    (K := Real.toNNReal (|K| * T + 4 * |K| + 4))
    (fun t ht => (lip K (Ioc_subset_Icc_self ht)).lipschitzOnWith)
    (fun t ht => (hY t ht).continuousWithinAt) (fun t ht => ?_) (fun _ _ => mem_univ _)
    (fun t ht => (hZ t ht).continuousWithinAt) (fun t ht => ?_) (fun _ _ => mem_univ _) hT'
  · have hmem : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
    refine (hY t hmem).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (Icc_mem_nhdsLE ht.1) (Icc_subset_Icc_right ht.2)
  · have hmem : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
    refine (hZ t hmem).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (Icc_mem_nhdsLE ht.1) (Icc_subset_Icc_right ht.2)

theorem exists_sol (K : ℝ) : ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = (0, 0, 0) ∧
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt Y (vS K t (Y t)) (Ici 0) t := by
  have hex : ∀ n : ℕ, ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = (0, 0, 0) ∧
      ∀ t ∈ Icc 0 ((n : ℝ) + 1), HasDerivWithinAt Y (vS K t (Y t)) (Icc 0 ((n : ℝ) + 1)) t :=
    fun n => local_sol K _ (by positivity)
  choose sol hsol0 hsol using hex
  have hag : ∀ k n : ℕ, ∀ s ∈ Icc (0 : ℝ) ((k : ℝ) + 1), s ≤ (n : ℝ) + 1 → sol k s = sol n s := by
    intro k n s hs hsn
    rcases le_total k n with hkn | hnk
    · have hkn' : (k : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hkn 1
      exact unique_right (by positivity) (hsol k)
        (fun t ht => (hsol n t ⟨ht.1, ht.2.trans hkn'⟩).mono (Icc_subset_Icc_right hkn'))
        ((hsol0 k).trans (hsol0 n).symm) hs
    · have hnk' : (n : ℝ) + 1 ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnk 1
      exact (unique_right (by positivity) (hsol n)
        (fun t ht => (hsol k t ⟨ht.1, ht.2.trans hnk'⟩).mono (Icc_subset_Icc_right hnk'))
        ((hsol0 n).trans (hsol0 k).symm) ⟨hs.1, hsn⟩).symm
  refine ⟨fun t => sol (⌈t⌉₊) t, ?_, fun t ht => ?_⟩
  · simp [hsol0]
  · set n := ⌈t⌉₊ with hn
    have htn : t ≤ (n : ℝ) := Nat.le_ceil t
    have hlt : t < (n : ℝ) + 1 := by linarith
    have heq : ∀ s ∈ Ico (0 : ℝ) ((n : ℝ) + 1), sol (⌈s⌉₊) s = sol n s := by
      intro s hs
      refine hag _ n s ⟨hs.1, ?_⟩ hs.2.le
      have := Nat.le_ceil s; linarith
    have hnhds : Ico (0 : ℝ) ((n : ℝ) + 1) ∈ nhdsWithin t (Ici 0) := by
      have : Iio ((n : ℝ) + 1) ∈ nhds t := Iio_mem_nhds hlt
      have h2 := inter_mem_nhdsWithin (Ici (0 : ℝ)) this
      refine Filter.mem_of_superset h2 ?_
      intro s hs; exact ⟨hs.1, hs.2⟩
    have hd := (hsol n t ⟨ht, hlt.le⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset hnhds (fun s hs => ⟨hs.1, hs.2.le⟩))
    have ht0 : sol (⌈t⌉₊) t = sol n t := rfl
    simp only
    rw [ht0]
    refine hd.congr_of_eventuallyEq ?_ (heq t ⟨ht, hlt⟩)
    exact Filter.mem_of_superset hnhds (fun s hs => heq s hs)

/-- The flow of the clamped coefficient-K field from (0, 0, 0). -/
noncomputable def flowK (K : ℝ) : ℝ → ℝ × ℝ × ℝ := Classical.choose (exists_sol K)

theorem flowK_zero (K : ℝ) : flowK K 0 = (0, 0, 0) := (Classical.choose_spec (exists_sol K)).1

theorem flowK_deriv (K : ℝ) :
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (flowK K) (vS K t (flowK K t)) (Ici 0) t :=
  (Classical.choose_spec (exists_sol K)).2


/-- The field difference between two coefficients: only the third component, bounded by
|K − K₀| · 2 (T + 2) on [0, T]. -/
theorem field_diff {T t : ℝ} (ht : t ∈ Icc 0 T) (K K₀ : ℝ) (y : ℝ × ℝ × ℝ) :
    dist (vS K t y) (vS K₀ t y) ≤ |K - K₀| * (2 * (T + 2)) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  set C := max t 0 + 2 with hC
  have hC0 : 0 ≤ C := by positivity
  have hCT : C ≤ T + 2 := by
    have : max t 0 ≤ T := max_le ht.2 hT
    linarith
  have hA : 0 ≤ |K - K₀| * (2 * (T + 2)) := mul_nonneg (abs_nonneg _) (by linarith)
  simp only [vS, Prod.dist_eq, Real.dist_eq, sub_self, abs_zero]
  refine max_le hA (max_le hA ?_)
  have e : -(K * cl C y.1 * cl 2 y.2.2) + 1 - cl 2 y.2.1 ^ 2 - (-(K₀ * cl C y.1 * cl 2 y.2.2) + 1 - cl 2 y.2.1 ^ 2)
      = -((K - K₀) * (cl C y.1 * cl 2 y.2.2)) := by ring
  rw [e, abs_neg, abs_mul, abs_mul]
  have h2 := abs_cl_le (by norm_num : (0 : ℝ) ≤ 2) y.2.2
  have h3 := abs_cl_le hC0 y.1
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  nlinarith [abs_nonneg (cl C y.1), abs_nonneg (cl 2 y.2.2)]

/-- Continuity of the flow in the coefficient K, uniformly on [0, T]. -/
theorem flowK_cont (T : ℝ) (hT : 0 ≤ T) (K₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ K, |K - K₀| < δ → ∀ t ∈ Icc 0 T, dist (flowK K t) (flowK K₀ t) < ε := by
  set L : ℝ := |K₀| * T + 4 * |K₀| + 4 with hL
  have hL0 : 0 < L := by have := abs_nonneg K₀; positivity
  set E : ℝ := Real.exp (L * T) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set A : ℝ := 2 * (T + 2) * E / L with hA
  have hA0 : 0 < A := by positivity
  refine ⟨ε / A, div_pos hε hA0, fun K hK t ht => ?_⟩
  have hd : ∀ (k : ℝ), ∀ s ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt (flowK k) (vS k s (flowK k s)) (Ici s) s := by
    intro k s hs
    refine (flowK_deriv k s hs.1).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset self_mem_nhdsWithin (fun u hu => hs.1.trans hu)
  have hc : ∀ k : ℝ, ContinuousOn (flowK k) (Icc 0 T) := fun k s hs =>
    ((flowK_deriv k s hs.1).continuousWithinAt).mono (fun u hu => hu.1)
  have h0 : dist (flowK K 0) (flowK K₀ 0) ≤ 0 := by
    rw [flowK_zero, flowK_zero, dist_self]
  have key := dist_le_of_approx_trajectories_ODE_of_mem (v := vS K₀) (s := fun _ => univ)
    (K := Real.toNNReal L) (εf := |K - K₀| * (2 * (T + 2))) (εg := 0)
    (fun s hs => (lip K₀ (Ico_subset_Icc_self hs)).lipschitzOnWith)
    (hc K) (hd K) (fun s hs => field_diff (Ico_subset_Icc_self hs) K K₀ _) (fun _ _ => mem_univ _)
    (hc K₀) (hd K₀) (fun s _ => by rw [dist_self]) (fun _ _ => mem_univ _) h0 t ht
  rw [Real.coe_toNNReal _ hL0.le, gronwallBound_of_K_ne_0 hL0.ne'] at key
  simp only [zero_mul, zero_add, add_zero, sub_zero] at key
  have hexp : Real.exp (L * t) ≤ E := by
    rw [hE]; apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left ht.2 hL0.le
  have hB : 0 ≤ |K - K₀| * (2 * (T + 2)) := mul_nonneg (abs_nonneg _) (by linarith)
  have h1 : |K - K₀| * (2 * (T + 2)) / L * (Real.exp (L * t) - 1) ≤ |K - K₀| * A := by
    have : |K - K₀| * (2 * (T + 2)) / L * (Real.exp (L * t) - 1) ≤ |K - K₀| * (2 * (T + 2)) / L * E :=
      mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hB hL0.le)
    refine this.trans (le_of_eq ?_)
    rw [hA]; field_simp
  have h2 : |K - K₀| * A < ε := by
    rw [lt_div_iff₀ hA0] at hK; linarith
  linarith

theorem of_chain {K : ℝ} {E : (ℝ → ℝ × ℝ × ℝ) → Prop} (h : ChainK K E) : E (flowK K) := by
  obtain ⟨T, _, hT⟩ := h
  exact hT (flowK K) (fun t ht => (flowK_deriv K t ht.1).mono Icc_subset_Ici_self) (flowK_zero K)

end Checked.FSSep.SFlow
