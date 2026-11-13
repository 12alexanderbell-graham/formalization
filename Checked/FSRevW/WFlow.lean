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
import Checked.FSRevW.WBase
import Checked.FSSep.SFlow

/-! Falkner–Skan adverse pressure gradient with a free scaled coefficient and a free shear clamp level: the global flow of the clamped field from (0, 0, α), its forward and backward uniqueness and its continuity in α. Ported from `Checked/FSSep/SFlow.lean`, `Checked/FSAtt/AFlow.lean` and `Checked/FSAtt/AAssemble.lean` by asserted text replacements (the Lipschitz and norm bounds carry the clamp level). Module `WFlow`, run 2026-11-13T0628Z. -/

namespace Checked.FSRevW.WFlow
open Set Checked.FSNeg.NBase Checked.FSSep.SBase Checked.FSRevW.WBase

theorem abs_cl_le' (c y : ℝ) : |cl c y| ≤ |c| := by
  unfold cl; rw [abs_le]
  refine ⟨?_, max_le (neg_le_abs c) ((min_le_left _ _).trans (le_abs_self c))⟩
  exact (neg_le_neg (le_abs_self c)).trans (le_max_left _ _)

theorem lip (Cq K : ℝ) {T t : ℝ} (ht : t ∈ Icc 0 T) :
    LipschitzWith (Real.toNNReal (|K| * T + (|Cq| + 2) * |K| + 4)) (vW Cq K t) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  have hK0 : 0 ≤ |K| := abs_nonneg K
  rw [Real.coe_toNNReal _ (by positivity)]
  simp only [vW, Prod.dist_eq, Real.dist_eq]
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
  · have := Checked.FSSep.SFlow.cl_sub 2 y.2.1 z.2.1; have hCq := abs_nonneg Cq; nlinarith [mul_nonneg hK0 hT, mul_nonneg (mul_nonneg hK0 hT) hm, mul_nonneg hK0 hm]
  · have := Checked.FSSep.SFlow.cl_sub Cq y.2.2 z.2.2; have hCq := abs_nonneg Cq; nlinarith [mul_nonneg hK0 hT, mul_nonneg (mul_nonneg hK0 hT) hm, mul_nonneg hK0 hm]
  · set a := cl C y.1
    set a' := cl C z.1
    set b := cl Cq y.2.2
    set b' := cl Cq z.2.2
    set c := cl 2 y.2.1
    set c' := cl 2 z.2.1
    have ha : |a - a'| ≤ |y.1 - z.1| := Checked.FSSep.SFlow.cl_sub C y.1 z.1
    have hb : |b - b'| ≤ |y.2.2 - z.2.2| := Checked.FSSep.SFlow.cl_sub Cq y.2.2 z.2.2
    have hc : |c - c'| ≤ |y.2.1 - z.2.1| := Checked.FSSep.SFlow.cl_sub 2 y.2.1 z.2.1
    have hbb : |b| ≤ |Cq| := abs_cl_le' _ _
    have haa : |a'| ≤ C := Checked.FSSep.SFlow.abs_cl_le hC0 _
    have hcc : |c| ≤ 2 := Checked.FSSep.SFlow.abs_cl_le (by norm_num) _
    have hcc' : |c'| ≤ 2 := Checked.FSSep.SFlow.abs_cl_le (by norm_num) _
    have e : -(K * a * b) + 1 - c ^ 2 - (-(K * a' * b') + 1 - c' ^ 2)
        = -(K * ((a - a') * b + a' * (b - b'))) + (c + c') * (c' - c) := by ring
    rw [abs_sub_comm] at hc
    rw [e]
    have h1 : |(a - a') * b| ≤ |Cq| * m := by
      rw [abs_mul, mul_comm]
      exact mul_le_mul hbb (ha.trans hd1) (abs_nonneg _) (abs_nonneg _)
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
    have h6 : |(a - a') * b + a' * (b - b')| ≤ (T + (|Cq| + 2)) * m := by nlinarith
    have h7 : |K| * |(a - a') * b + a' * (b - b')| ≤ |K| * ((T + (|Cq| + 2)) * m) :=
      mul_le_mul_of_nonneg_left h6 hK0
    nlinarith [mul_nonneg hK0 hm]

theorem norm_le (Cq K : ℝ) {T t : ℝ} (ht : t ∈ Icc 0 T) (y : ℝ × ℝ × ℝ) :
    ‖vW Cq K t y‖ ≤ |Cq| * |K| * T + 2 * |Cq| * |K| + |Cq| + 5 := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  simp only [vW, Prod.norm_def, Real.norm_eq_abs]
  set C := max t 0 + 2 with hC
  have hC0 : 0 ≤ C := by positivity
  have hCT : C ≤ T + 2 := by
    have : max t 0 ≤ T := max_le ht.2 hT
    nlinarith
  have h1 := Checked.FSSep.SFlow.abs_cl_le (by norm_num : (0 : ℝ) ≤ 2) y.2.1
  have h2 := abs_cl_le' Cq y.2.2
  have hCq := abs_nonneg Cq
  have h3 := Checked.FSSep.SFlow.abs_cl_le hC0 y.1
  have hK0 : 0 ≤ |K| := abs_nonneg K
  have hKT : 0 ≤ |K| * T := mul_nonneg hK0 hT
  have hKTC : 0 ≤ |Cq| * |K| * T := by positivity
  have hKC : 0 ≤ |Cq| * |K| := by positivity
  refine max_le (by linarith) (max_le (by linarith) ?_)
  have hab : |K * cl C y.1 * cl Cq y.2.2| ≤ |K| * (C * |Cq|) := by
    rw [abs_mul, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul h3 h2 (abs_nonneg _) hC0) hK0
  have hab2 : |K| * (C * |Cq|) ≤ |K| * ((T + 2) * |Cq|) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hCq) hK0
  have hsq : |cl 2 y.2.1 ^ 2| ≤ 4 := by
    rw [abs_pow]; nlinarith [abs_nonneg (cl 2 y.2.1)]
  have k1 := abs_sub (-(K * cl C y.1 * cl Cq y.2.2) + 1) (cl 2 y.2.1 ^ 2)
  have k2 := abs_add_le (-(K * cl C y.1 * cl Cq y.2.2)) 1
  rw [abs_neg] at k2
  simp only [abs_one] at k2
  nlinarith

theorem cont (Cq K : ℝ) (y : ℝ × ℝ × ℝ) : Continuous (fun t => vW Cq K t y) := by
  unfold vW cl
  fun_prop

/-- Forward uniqueness on [0, T]. -/
theorem unique_right {Cq K T : ℝ} (hT : 0 ≤ T) {Y Z : ℝ → ℝ × ℝ × ℝ}
    (hY : ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vW Cq K t (Y t)) (Icc 0 T) t)
    (hZ : ∀ t ∈ Icc 0 T, HasDerivWithinAt Z (vW Cq K t (Z t)) (Icc 0 T) t)
    (h0 : Y 0 = Z 0) : EqOn Y Z (Icc 0 T) := by
  refine ODE_solution_unique_of_mem_Icc_right (v := vW Cq K) (s := fun _ => univ)
    (K := Real.toNNReal (|K| * T + (|Cq| + 2) * |K| + 4))
    (fun t ht => (lip Cq K (Ico_subset_Icc_self ht)).lipschitzOnWith)
    (fun t ht => (hY t ht).continuousWithinAt) (fun t ht => ?_) (fun _ _ => mem_univ _)
    (fun t ht => (hZ t ht).continuousWithinAt) (fun t ht => ?_) (fun _ _ => mem_univ _) h0
  · have hmem : t ∈ Icc 0 T := ⟨ht.1, ht.2.le⟩
    refine (hY t hmem).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)
  · have hmem : t ∈ Icc 0 T := ⟨ht.1, ht.2.le⟩
    refine (hZ t hmem).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)

/-- Backward uniqueness on [0, T]. -/
theorem unique_left {Cq K T : ℝ} (hT : 0 ≤ T) {Y Z : ℝ → ℝ × ℝ × ℝ}
    (hY : ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vW Cq K t (Y t)) (Icc 0 T) t)
    (hZ : ∀ t ∈ Icc 0 T, HasDerivWithinAt Z (vW Cq K t (Z t)) (Icc 0 T) t)
    (hT' : Y T = Z T) : EqOn Y Z (Icc 0 T) := by
  refine ODE_solution_unique_of_mem_Icc_left (v := vW Cq K) (s := fun _ => univ)
    (K := Real.toNNReal (|K| * T + (|Cq| + 2) * |K| + 4))
    (fun t ht => (lip Cq K (Ioc_subset_Icc_self ht)).lipschitzOnWith)
    (fun t ht => (hY t ht).continuousWithinAt) (fun t ht => ?_) (fun _ _ => mem_univ _)
    (fun t ht => (hZ t ht).continuousWithinAt) (fun t ht => ?_) (fun _ _ => mem_univ _) hT'
  · have hmem : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
    refine (hY t hmem).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (Icc_mem_nhdsLE ht.1) (Icc_subset_Icc_right ht.2)
  · have hmem : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
    refine (hZ t hmem).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (Icc_mem_nhdsLE ht.1) (Icc_subset_Icc_right ht.2)

theorem local_sol (Cq K α T : ℝ) (hT : 0 < T) : ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = (0, 0, α) ∧
    ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vW Cq K t (Y t)) (Icc 0 T) t := by
  set L : ℝ := |Cq| * |K| * T + 2 * |Cq| * |K| + |Cq| + 5 with hL
  have hL0 : 0 ≤ L := by positivity
  have hPL : IsPicardLindelof (vW Cq K) (tmin := 0) (tmax := T) ⟨0, le_rfl, hT.le⟩
      ((0 : ℝ), (0 : ℝ), α) (Real.toNNReal (L * T)) 0 (Real.toNNReal L)
      (Real.toNNReal (|K| * T + (|Cq| + 2) * |K| + 4)) :=
    { lipschitzOnWith := fun t ht => (lip Cq K ht).lipschitzOnWith
      continuousOn := fun x _ => (cont Cq K x).continuousOn
      norm_le := fun t ht p _ => by
        rw [Real.coe_toNNReal _ hL0]; exact norm_le Cq K ht p
      mul_max_le := by
        rw [Real.coe_toNNReal _ hL0, Real.coe_toNNReal _ (by positivity)]
        simp only [NNReal.coe_zero, sub_zero, sub_self]
        rw [max_eq_left hT.le] }
  exact hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

theorem exists_sol (Cq K α : ℝ) : ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = (0, 0, α) ∧
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt Y (vW Cq K t (Y t)) (Ici 0) t := by
  have hex : ∀ n : ℕ, ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = (0, 0, α) ∧
      ∀ t ∈ Icc 0 ((n : ℝ) + 1), HasDerivWithinAt Y (vW Cq K t (Y t)) (Icc 0 ((n : ℝ) + 1)) t :=
    fun n => local_sol Cq K α _ (by positivity)
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

/-- The flow of the clamped field (shear clamp `Cq`) from (0, 0, α). -/
noncomputable def flowW (Cq K α : ℝ) : ℝ → ℝ × ℝ × ℝ := Classical.choose (exists_sol Cq K α)

theorem flowW_zero (Cq K α : ℝ) : flowW Cq K α 0 = (0, 0, α) := (Classical.choose_spec (exists_sol Cq K α)).1

theorem flowW_deriv (Cq K α : ℝ) :
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (flowW Cq K α) (vW Cq K t (flowW Cq K α t)) (Ici 0) t :=
  (Classical.choose_spec (exists_sol Cq K α)).2

/-- Continuity of the flow in α, uniformly on [0, T]. -/
theorem flowW_cont (Cq K T : ℝ) (hT : 0 ≤ T) (α₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ α, |α - α₀| < δ → ∀ t ∈ Icc 0 T, dist (flowW Cq K α t) (flowW Cq K α₀ t) < ε := by
  set L : ℝ := |K| * T + (|Cq| + 2) * |K| + 4 with hL
  set E : ℝ := Real.exp (L * T) with hE
  have hE0 : 0 < E := Real.exp_pos _
  refine ⟨ε / E, div_pos hε hE0, fun α hα t ht => ?_⟩
  have hd : ∀ (β : ℝ), ∀ s ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt (flowW Cq K β) (vW Cq K s (flowW Cq K β s)) (Ici s) s := by
    intro β s hs
    refine (flowW_deriv Cq K β s hs.1).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset self_mem_nhdsWithin (fun u hu => hs.1.trans hu)
  have hc : ∀ β : ℝ, ContinuousOn (flowW Cq K β) (Icc 0 T) := fun β s hs =>
    ((flowW_deriv Cq K β s hs.1).continuousWithinAt).mono (fun u hu => hu.1)
  have h0 : dist (flowW Cq K α 0) (flowW Cq K α₀ 0) ≤ |α - α₀| := by
    rw [flowW_zero, flowW_zero]
    simp [Prod.dist_eq, Real.dist_eq]
  have key := dist_le_of_trajectories_ODE_of_mem (v := vW Cq K) (s := fun _ => univ)
    (K := Real.toNNReal L) (fun s hs => (lip Cq K (Ico_subset_Icc_self hs)).lipschitzOnWith)
    (hc α) (hd α) (fun _ _ => mem_univ _) (hc α₀) (hd α₀) (fun _ _ => mem_univ _) h0 t ht
  have hL0 : 0 ≤ L := by positivity
  rw [Real.coe_toNNReal _ hL0] at key
  have hexp : Real.exp (L * (t - 0)) ≤ E := by
    rw [hE]; apply Real.exp_le_exp.mpr
    have : t - 0 ≤ T := by linarith [ht.2]
    exact mul_le_mul_of_nonneg_left this hL0
  have h1 : |α - α₀| * Real.exp (L * (t - 0)) ≤ |α - α₀| * E :=
    mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
  have h2 : |α - α₀| * E < ε := by
    rw [lt_div_iff₀ hE0] at hα; exact hα
  linarith

theorem comps (Cq K α : ℝ) :
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => (flowW Cq K α t).1) (cl 2 (flowW Cq K α η).2.1) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => (flowW Cq K α t).2.1) (cl Cq (flowW Cq K α η).2.2) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => (flowW Cq K α t).2.2)
      (-(K * cl (max η 0 + 2) (flowW Cq K α η).1 * cl Cq (flowW Cq K α η).2.2) + 1 - cl 2 (flowW Cq K α η).2.1 ^ 2)
      (Ici 0) η) := by
  refine ⟨fun η hη => ?_, fun η hη => ?_, fun η hη => ?_⟩
  · exact (hasFDerivAt_fst.comp_hasDerivWithinAt η (flowW_deriv Cq K α η hη))
  · exact (hasFDerivAt_fst.comp_hasDerivWithinAt η
      (hasFDerivAt_snd.comp_hasDerivWithinAt η (flowW_deriv Cq K α η hη)))
  · exact (hasFDerivAt_snd.comp_hasDerivWithinAt η
      (hasFDerivAt_snd.comp_hasDerivWithinAt η (flowW_deriv Cq K α η hη)))

theorem of_chain {Cq K α : ℝ} {E : (ℝ → ℝ × ℝ × ℝ) → Prop} (h : ChainW Cq K α E) : E (flowW Cq K α) := by
  obtain ⟨T, _, hT⟩ := h
  exact hT (flowW Cq K α) (fun t ht => (flowW_deriv Cq K α t ht.1).mono Icc_subset_Ici_self) (flowW_zero Cq K α)

theorem dist_c0 {a b : ℝ × ℝ × ℝ} : |a.1 - b.1| ≤ dist a b := by
  rw [← Real.dist_eq, Prod.dist_eq]; exact le_max_left _ _

theorem dist_c1 {a b : ℝ × ℝ × ℝ} : |a.2.1 - b.2.1| ≤ dist a b := by
  have h1 : dist a.2 b.2 ≤ dist a b := by rw [Prod.dist_eq]; exact le_max_right _ _
  have h2 : dist a.2.1 b.2.1 ≤ dist a.2 b.2 := by rw [Prod.dist_eq]; exact le_max_left _ _
  rw [← Real.dist_eq]; linarith

theorem dist_c2 {a b : ℝ × ℝ × ℝ} : |a.2.2 - b.2.2| ≤ dist a b := by
  have h1 : dist a.2 b.2 ≤ dist a b := by rw [Prod.dist_eq]; exact le_max_right _ _
  have h2 : dist a.2.2 b.2.2 ≤ dist a.2 b.2 := by rw [Prod.dist_eq]; exact le_max_right _ _
  rw [← Real.dist_eq]; linarith

theorem cont_comp (Cq K α : ℝ) (η : ℝ) : ContinuousOn (flowW Cq K α) (Icc 0 η) := fun s hs =>
  ((flowW_deriv Cq K α s hs.1).continuousWithinAt).mono (fun x hx => hx.1)

theorem over_open (Cq K α₀ : ℝ) (h : Over (flowW Cq K α₀)) :
    ∃ δ > 0, ∀ α, |α - α₀| < δ → Over (flowW Cq K α) := by
  obtain ⟨η, hη, hp⟩ := h
  obtain ⟨δ, hδ, hcl⟩ := flowW_cont Cq K η hη.le α₀ (show 0 < (flowW Cq K α₀ η).2.1 - 1 by linarith)
  refine ⟨δ, hδ, fun α hα => ⟨η, hη, ?_⟩⟩
  have k := (dist_c1 (a := flowW Cq K α η) (b := flowW Cq K α₀ η)).trans_lt (hcl α hα η ⟨hη.le, le_rfl⟩)
  rw [abs_lt] at k; linarith [k.1]

end Checked.FSRevW.WFlow
