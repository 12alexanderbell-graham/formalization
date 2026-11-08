import Mathlib
import Work.FSFifth.F5ExBase

/-!
# K = 5 (Falkner–Skan β = 1/5, scaled) existence: a global flow of the clamped field (run 2026-11-08T2028Z, ported from Work.Homann, itself ported from `Work.Hiemenz.HExFlow`)

`exists_sol`: the clamped K = 5 (Falkner–Skan β = 1/5, scaled) field `vH` (bounded and Lipschitz on every [0, T]) has a
solution on [0, ∞) from (0, 0, α) for every α, with derivatives within [0, ∞) (Picard–Lindelöf on
[0, n + 1] for every n, glued by forward uniqueness). `flow α` is such a solution; `unique_left`
and `unique_right` are backward and forward uniqueness on [0, T]; `flow_cont` is continuity of
the flow in α, uniformly on [0, T] (Grönwall).
-/

namespace Work.FSFifth.F5ExFlow
open Set Work.FSFifth.F5ExBase

theorem cl_sub (c y z : ℝ) : |cl c y - cl c z| ≤ |y - z| := by
  unfold cl
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp) ?_)
  exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by simp) le_rfl)

theorem abs_cl_le {c : ℝ} (hc : 0 ≤ c) (y : ℝ) : |cl c y| ≤ c := by
  unfold cl; rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem lip {T t : ℝ} (ht : t ∈ Icc 0 T) :
    LipschitzWith (Real.toNNReal (5 * T + 24)) (vH t) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  rw [Real.coe_toNNReal _ (by linarith)]
  simp only [vH, Prod.dist_eq, Real.dist_eq]
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
  · have := cl_sub 2 y.2.1 z.2.1; nlinarith
  · have := cl_sub 2 y.2.2 z.2.2; nlinarith
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
    have e : -(5 * a * b) - 1 + c ^ 2 - (-(5 * a' * b') - 1 + c' ^ 2)
        = -(5 * ((a - a') * b + a' * (b - b'))) + (c + c') * (c - c') := by ring
    rw [e]
    have h1 : |(a - a') * b| ≤ 2 * m := by
      rw [abs_mul, mul_comm]
      exact mul_le_mul hbb (ha.trans hd1) (abs_nonneg _) (by norm_num)
    have h2 : |a' * (b - b')| ≤ C * m := by
      rw [abs_mul]
      exact mul_le_mul haa (hb.trans hd3) (abs_nonneg _) hC0
    have h4 : |(c + c') * (c - c')| ≤ 4 * m := by
      rw [abs_mul]
      have : |c + c'| ≤ 4 := (abs_add_le c c').trans (by linarith)
      exact mul_le_mul this (hc.trans hd2) (abs_nonneg _) (by norm_num)
    have h3 := abs_add_le ((a - a') * b) (a' * (b - b'))
    have h5 := abs_add_le (-(5 * ((a - a') * b + a' * (b - b')))) ((c + c') * (c - c'))
    rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5)] at h5
    nlinarith

theorem norm_le {T t : ℝ} (ht : t ∈ Icc 0 T) (y : ℝ × ℝ × ℝ) : ‖vH t y‖ ≤ 10 * T + 25 := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  simp only [vH, Prod.norm_def, Real.norm_eq_abs]
  set C := max t 0 + 2 with hC
  have hC0 : 0 ≤ C := by positivity
  have hCT : C ≤ T + 2 := by
    have : max t 0 ≤ T := max_le ht.2 hT
    linarith
  have h1 := abs_cl_le (by norm_num : (0 : ℝ) ≤ 2) y.2.1
  have h2 := abs_cl_le (by norm_num : (0 : ℝ) ≤ 2) y.2.2
  have h3 := abs_cl_le hC0 y.1
  refine max_le (by linarith) (max_le (by linarith) ?_)
  have hab : |5 * cl C y.1 * cl 2 y.2.2| ≤ 5 * C * 2 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5)]; nlinarith [abs_nonneg (cl C y.1), abs_nonneg (cl 2 y.2.2)]
  have hsq : |cl 2 y.2.1 ^ 2| ≤ 4 := by
    rw [abs_pow]; nlinarith [abs_nonneg (cl 2 y.2.1)]
  have k1 := abs_add_le (-(5 * cl C y.1 * cl 2 y.2.2) - 1) (cl 2 y.2.1 ^ 2)
  have k2 := abs_sub (-(5 * cl C y.1 * cl 2 y.2.2)) 1
  rw [abs_neg] at k2
  simp only [abs_one] at k2
  linarith

theorem cont (y : ℝ × ℝ × ℝ) : Continuous (fun t => vH t y) := by
  unfold vH cl
  fun_prop

/-- A solution on [0, T] for every T > 0. -/
theorem local_sol (α T : ℝ) (hT : 0 < T) : ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = (0, 0, α) ∧
    ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vH t (Y t)) (Icc 0 T) t := by
  set L : ℝ := 10 * T + 25 with hL
  have hL0 : 0 ≤ L := by positivity
  have hPL : IsPicardLindelof vH (tmin := 0) (tmax := T) ⟨0, le_rfl, hT.le⟩
      ((0 : ℝ), (0 : ℝ), α) (Real.toNNReal (L * T)) 0 (Real.toNNReal L)
      (Real.toNNReal (5 * T + 24)) :=
    { lipschitzOnWith := fun t ht => (lip ht).lipschitzOnWith
      continuousOn := fun x _ => (cont x).continuousOn
      norm_le := fun t ht p _ => by
        rw [Real.coe_toNNReal _ hL0]; exact norm_le ht p
      mul_max_le := by
        rw [Real.coe_toNNReal _ hL0, Real.coe_toNNReal _ (by positivity)]
        simp only [NNReal.coe_zero, sub_zero, sub_self]
        rw [max_eq_left hT.le] }
  exact hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- Forward uniqueness on [0, T]. -/
theorem unique_right {T : ℝ} (hT : 0 ≤ T) {Y Z : ℝ → ℝ × ℝ × ℝ}
    (hY : ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vH t (Y t)) (Icc 0 T) t)
    (hZ : ∀ t ∈ Icc 0 T, HasDerivWithinAt Z (vH t (Z t)) (Icc 0 T) t)
    (h0 : Y 0 = Z 0) : EqOn Y Z (Icc 0 T) := by
  refine ODE_solution_unique_of_mem_Icc_right (v := vH) (s := fun _ => univ)
    (K := Real.toNNReal (5 * T + 24))
    (fun t ht => (lip (Ico_subset_Icc_self ht)).lipschitzOnWith)
    (fun t ht => (hY t ht).continuousWithinAt) (fun t ht => ?_) (fun _ _ => mem_univ _)
    (fun t ht => (hZ t ht).continuousWithinAt) (fun t ht => ?_) (fun _ _ => mem_univ _) h0
  · have hmem : t ∈ Icc 0 T := ⟨ht.1, ht.2.le⟩
    refine (hY t hmem).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)
  · have hmem : t ∈ Icc 0 T := ⟨ht.1, ht.2.le⟩
    refine (hZ t hmem).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)

/-- Backward uniqueness on [0, T]. -/
theorem unique_left {T : ℝ} (hT : 0 ≤ T) {Y Z : ℝ → ℝ × ℝ × ℝ}
    (hY : ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vH t (Y t)) (Icc 0 T) t)
    (hZ : ∀ t ∈ Icc 0 T, HasDerivWithinAt Z (vH t (Z t)) (Icc 0 T) t)
    (hT' : Y T = Z T) : EqOn Y Z (Icc 0 T) := by
  refine ODE_solution_unique_of_mem_Icc_left (v := vH) (s := fun _ => univ)
    (K := Real.toNNReal (5 * T + 24))
    (fun t ht => (lip (Ioc_subset_Icc_self ht)).lipschitzOnWith)
    (fun t ht => (hY t ht).continuousWithinAt) (fun t ht => ?_) (fun _ _ => mem_univ _)
    (fun t ht => (hZ t ht).continuousWithinAt) (fun t ht => ?_) (fun _ _ => mem_univ _) hT'
  · have hmem : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
    refine (hY t hmem).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (Icc_mem_nhdsLE ht.1) (Icc_subset_Icc_right ht.2)
  · have hmem : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
    refine (hZ t hmem).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (Icc_mem_nhdsLE ht.1) (Icc_subset_Icc_right ht.2)

theorem exists_sol (α : ℝ) : ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = (0, 0, α) ∧
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt Y (vH t (Y t)) (Ici 0) t := by
  have hex : ∀ n : ℕ, ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = (0, 0, α) ∧
      ∀ t ∈ Icc 0 ((n : ℝ) + 1), HasDerivWithinAt Y (vH t (Y t)) (Icc 0 ((n : ℝ) + 1)) t :=
    fun n => local_sol α _ (by positivity)
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

/-- The flow of the clamped field from (0, 0, α). -/
noncomputable def flow (α : ℝ) : ℝ → ℝ × ℝ × ℝ := Classical.choose (exists_sol α)

theorem flow_zero (α : ℝ) : flow α 0 = (0, 0, α) := (Classical.choose_spec (exists_sol α)).1

theorem flow_deriv (α : ℝ) :
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (flow α) (vH t (flow α t)) (Ici 0) t :=
  (Classical.choose_spec (exists_sol α)).2

/-- Continuity of the flow in α, uniformly on [0, T]. -/
theorem flow_cont (T : ℝ) (hT : 0 ≤ T) (α₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ α, |α - α₀| < δ → ∀ t ∈ Icc 0 T, dist (flow α t) (flow α₀ t) < ε := by
  set K : ℝ := 5 * T + 24 with hK
  set E : ℝ := Real.exp (K * T) with hE
  have hE0 : 0 < E := Real.exp_pos _
  refine ⟨ε / E, div_pos hε hE0, fun α hα t ht => ?_⟩
  have hd : ∀ (β : ℝ), ∀ s ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt (flow β) (vH s (flow β s)) (Ici s) s := by
    intro β s hs
    refine (flow_deriv β s hs.1).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset self_mem_nhdsWithin (fun u hu => hs.1.trans hu)
  have hc : ∀ β : ℝ, ContinuousOn (flow β) (Icc 0 T) := fun β s hs =>
    ((flow_deriv β s hs.1).continuousWithinAt).mono (fun u hu => hu.1)
  have h0 : dist (flow α 0) (flow α₀ 0) ≤ |α - α₀| := by
    rw [flow_zero, flow_zero]
    simp [Prod.dist_eq, Real.dist_eq]
  have key := dist_le_of_trajectories_ODE_of_mem (v := vH) (s := fun _ => univ)
    (K := Real.toNNReal K) (fun s hs => (lip (Ico_subset_Icc_self hs)).lipschitzOnWith)
    (hc α) (hd α) (fun _ _ => mem_univ _) (hc α₀) (hd α₀) (fun _ _ => mem_univ _) h0 t ht
  rw [Real.coe_toNNReal _ (by linarith)] at key
  have hexp : Real.exp (K * (t - 0)) ≤ E := by
    rw [hE]; apply Real.exp_le_exp.mpr
    have : t - 0 ≤ T := by linarith [ht.2]
    exact mul_le_mul_of_nonneg_left this (by linarith)
  have h1 : |α - α₀| * Real.exp (K * (t - 0)) ≤ |α - α₀| * E :=
    mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
  have h2 : |α - α₀| * E < ε := by
    rw [lt_div_iff₀ hE0] at hα; exact hα
  linarith

end Work.FSFifth.F5ExFlow
