import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Checked.Blasius.BExBase
/-! Blasius boundary layer, `BExFlow`: a global solution of the clamped Blasius system from the wall state with unit value of q. Promoted from `Work/Blasius/BExFlow.lean`. -/

namespace Checked.Blasius.BExFlow
open Set Checked.Blasius.BExBase

theorem cl_sub (c y z : ℝ) : |cl c y - cl c z| ≤ |y - z| := by
  unfold cl
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp) ?_)
  exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by simp) le_rfl)

theorem abs_cl_le {c : ℝ} (hc : 0 ≤ c) (y : ℝ) : |cl c y| ≤ c := by
  unfold cl; rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem lip {T t : ℝ} (ht : t ∈ Icc 0 T) :
    LipschitzWith (Real.toNNReal (4 * T + 2)) (vF t) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  rw [Real.coe_toNNReal _ (by linarith)]
  simp only [vF, Prod.dist_eq, Real.dist_eq]
  set m := max |y.1 - z.1| (max |y.2.1 - z.2.1| |y.2.2 - z.2.2|)
  have hd1 : |y.1 - z.1| ≤ m := le_max_left _ _
  have hd2 : |y.2.1 - z.2.1| ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hd3 : |y.2.2 - z.2.2| ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  have hm : 0 ≤ m := (abs_nonneg _).trans hd1
  set C := 4 * max t 0 + 1 with hC
  have hC0 : 0 ≤ C := by positivity
  have hCT : C ≤ 4 * T + 1 := by
    have : max t 0 ≤ T := max_le ht.2 hT
    linarith
  refine max_le ?_ (max_le ?_ ?_)
  · have := cl_sub 4 y.2.1 z.2.1; nlinarith
  · have := cl_sub 2 y.2.2 z.2.2; nlinarith
  · set a := cl C y.1
    set a' := cl C z.1
    set b := cl 2 y.2.2
    set b' := cl 2 z.2.2
    have ha : |a - a'| ≤ |y.1 - z.1| := cl_sub C y.1 z.1
    have hb : |b - b'| ≤ |y.2.2 - z.2.2| := cl_sub 2 y.2.2 z.2.2
    have hbb : |b| ≤ 2 := abs_cl_le (by norm_num) _
    have haa : |a'| ≤ C := abs_cl_le hC0 _
    have e : -(a * b / 2) - -(a' * b' / 2) = -((a - a') * b + a' * (b - b')) / 2 := by ring
    rw [e, abs_div, abs_neg, abs_two]
    have h1 : |(a - a') * b| ≤ 2 * m := by
      rw [abs_mul, mul_comm]
      exact mul_le_mul hbb (ha.trans hd1) (abs_nonneg _) (by norm_num)
    have h2 : |a' * (b - b')| ≤ C * m := by
      rw [abs_mul]
      exact mul_le_mul haa (hb.trans hd3) (abs_nonneg _) hC0
    have h3 := abs_add_le ((a - a') * b) (a' * (b - b'))
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    nlinarith

theorem norm_le {T t : ℝ} (ht : t ∈ Icc 0 T) (y : ℝ × ℝ × ℝ) : ‖vF t y‖ ≤ 4 * T + 5 := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  simp only [vF, Prod.norm_def, Real.norm_eq_abs]
  set C := 4 * max t 0 + 1 with hC
  have hC0 : 0 ≤ C := by positivity
  have hCT : C ≤ 4 * T + 1 := by
    have : max t 0 ≤ T := max_le ht.2 hT
    linarith
  have h1 := abs_cl_le (by norm_num : (0 : ℝ) ≤ 4) y.2.1
  have h2 := abs_cl_le (by norm_num : (0 : ℝ) ≤ 2) y.2.2
  have h3 := abs_cl_le hC0 y.1
  refine max_le (by linarith) (max_le (by linarith) ?_)
  rw [abs_neg, abs_div, abs_two, abs_mul]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  nlinarith [abs_nonneg (cl C y.1), abs_nonneg (cl 2 y.2.2)]

theorem cont (y : ℝ × ℝ × ℝ) : Continuous (fun t => vF t y) := by
  unfold vF cl
  fun_prop

/-- A solution on [0, T] for every T > 0. -/
theorem local_sol (T : ℝ) (hT : 0 < T) : ∃ α : ℝ → ℝ × ℝ × ℝ, α 0 = (0, 0, 1) ∧
    ∀ t ∈ Icc 0 T, HasDerivWithinAt α (vF t (α t)) (Icc 0 T) t := by
  set L : ℝ := 4 * T + 5 with hL
  have hL0 : 0 ≤ L := by positivity
  have hPL : IsPicardLindelof vF (tmin := 0) (tmax := T) ⟨0, le_rfl, hT.le⟩
      ((0 : ℝ), (0 : ℝ), (1 : ℝ)) (Real.toNNReal (L * T)) 0 (Real.toNNReal L)
      (Real.toNNReal (4 * T + 2)) :=
    { lipschitzOnWith := fun t ht => (lip ht).lipschitzOnWith
      continuousOn := fun x _ => (cont x).continuousOn
      norm_le := fun t ht p _ => by
        rw [Real.coe_toNNReal _ hL0]; exact norm_le ht p
      mul_max_le := by
        rw [Real.coe_toNNReal _ hL0, Real.coe_toNNReal _ (by positivity)]
        simp only [NNReal.coe_zero, sub_zero, sub_self]
        rw [max_eq_left hT.le] }
  exact hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

theorem agree {T T' : ℝ} (hT : 0 < T) (hTT' : T ≤ T') (f g : ℝ → ℝ × ℝ × ℝ) (h0 : f 0 = g 0)
    (hf : ∀ t ∈ Icc 0 T, HasDerivWithinAt f (vF t (f t)) (Icc 0 T) t)
    (hg : ∀ t ∈ Icc 0 T', HasDerivWithinAt g (vF t (g t)) (Icc 0 T') t) :
    EqOn f g (Icc 0 T) := by
  refine ODE_solution_unique_of_mem_Icc_right (v := vF) (s := fun _ => univ)
    (K := Real.toNNReal (4 * T + 2))
    (fun t ht => (lip (Ico_subset_Icc_self ht)).lipschitzOnWith)
    (fun t ht => (hf t ht).continuousWithinAt) (fun t ht => ?_) (fun _ _ => mem_univ _)
    (fun t ht => ((hg t ⟨ht.1, ht.2.trans hTT'⟩).continuousWithinAt.mono
      (Icc_subset_Icc_right hTT'))) (fun t ht => ?_) (fun _ _ => mem_univ _) h0
  · have hmem : t ∈ Icc 0 T := ⟨ht.1, ht.2.le⟩
    refine (hf t hmem).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)
  · have hmem : t ∈ Icc 0 T' := ⟨ht.1, ht.2.le.trans hTT'⟩
    refine (hg t hmem).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (Icc_mem_nhdsGE (lt_of_lt_of_le ht.2 hTT'))
      (Icc_subset_Icc_left ht.1)

theorem exists_flow : ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = (0, 0, 1) ∧
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt Y (vF t (Y t)) (Ici 0) t := by
  have hex : ∀ n : ℕ, ∃ α : ℝ → ℝ × ℝ × ℝ, α 0 = (0, 0, 1) ∧
      ∀ t ∈ Icc 0 ((n : ℝ) + 1), HasDerivWithinAt α (vF t (α t)) (Icc 0 ((n : ℝ) + 1)) t :=
    fun n => local_sol _ (by positivity)
  choose sol hsol0 hsol using hex
  -- any two solutions agree where both are defined
  have hag : ∀ k n : ℕ, ∀ s ∈ Icc (0 : ℝ) ((k : ℝ) + 1), s ≤ (n : ℝ) + 1 → sol k s = sol n s := by
    intro k n s hs hsn
    rcases le_total k n with hkn | hnk
    · exact agree (by positivity) (by exact_mod_cast (Nat.add_le_add_right hkn 1))
        (sol k) (sol n) ((hsol0 k).trans (hsol0 n).symm) (hsol k) (hsol n) hs
    · exact (agree (by positivity) (by exact_mod_cast (Nat.add_le_add_right hnk 1))
        (sol n) (sol k) ((hsol0 n).trans (hsol0 k).symm) (hsol n) (hsol k) ⟨hs.1, hsn⟩).symm
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

end Checked.Blasius.BExFlow
