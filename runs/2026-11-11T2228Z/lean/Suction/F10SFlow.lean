import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Checked.FSTenth.F10ExFlow
/-! Scratch (run 2026-11-11T2228Z): the clamped K = 10 (Falkner–Skan β = 1/10, scaled) flow from (a0, 0, α), ported from
`Checked/FSTenth/F10ExFlow.lean` by `runs/2026-11-11T2228Z/scripts/port_suction_all.py`. -/

namespace Work.Suction.F10SFlow
open Set Checked.FSTenth.F10ExBase Checked.FSTenth.F10ExFlow

/-- A solution on [0, T] for every T > 0. -/
theorem local_solS (a0 α T : ℝ) (hT : 0 < T) : ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = (a0, 0, α) ∧
    ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vH t (Y t)) (Icc 0 T) t := by
  set L : ℝ := 20 * T + 45 with hL
  have hL0 : 0 ≤ L := by positivity
  have hPL : IsPicardLindelof vH (tmin := 0) (tmax := T) ⟨0, le_rfl, hT.le⟩
      (a0, (0 : ℝ), α) (Real.toNNReal (L * T)) 0 (Real.toNNReal L)
      (Real.toNNReal (10 * T + 44)) :=
    { lipschitzOnWith := fun t ht => (lip ht).lipschitzOnWith
      continuousOn := fun x _ => (cont x).continuousOn
      norm_le := fun t ht p _ => by
        rw [Real.coe_toNNReal _ hL0]; exact norm_le ht p
      mul_max_le := by
        rw [Real.coe_toNNReal _ hL0, Real.coe_toNNReal _ (by positivity)]
        simp only [NNReal.coe_zero, sub_zero, sub_self]
        rw [max_eq_left hT.le] }
  exact hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

theorem exists_solS (a0 α : ℝ) : ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = (a0, 0, α) ∧
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt Y (vH t (Y t)) (Ici 0) t := by
  have hex : ∀ n : ℕ, ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = (a0, 0, α) ∧
      ∀ t ∈ Icc 0 ((n : ℝ) + 1), HasDerivWithinAt Y (vH t (Y t)) (Icc 0 ((n : ℝ) + 1)) t :=
    fun n => local_solS a0 α _ (by positivity)
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

/-- The flow of the clamped field from (a0, 0, α). -/
noncomputable def flowS (a0 α : ℝ) : ℝ → ℝ × ℝ × ℝ := Classical.choose (exists_solS a0 α)

theorem flowS_zero (a0 α : ℝ) : flowS a0 α 0 = (a0, 0, α) := (Classical.choose_spec (exists_solS a0 α)).1

theorem flowS_deriv (a0 α : ℝ) :
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (flowS a0 α) (vH t (flowS a0 α t)) (Ici 0) t :=
  (Classical.choose_spec (exists_solS a0 α)).2

/-- Continuity of the flow in α, uniformly on [0, T]. -/
theorem flowS_cont (a0 : ℝ) (T : ℝ) (hT : 0 ≤ T) (α₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ α, |α - α₀| < δ → ∀ t ∈ Icc 0 T, dist (flowS a0 α t) (flowS a0 α₀ t) < ε := by
  set K : ℝ := 10 * T + 44 with hK
  set E : ℝ := Real.exp (K * T) with hE
  have hE0 : 0 < E := Real.exp_pos _
  refine ⟨ε / E, div_pos hε hE0, fun α hα t ht => ?_⟩
  have hd : ∀ (β : ℝ), ∀ s ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt (flowS a0 β) (vH s (flowS a0 β s)) (Ici s) s := by
    intro β s hs
    refine (flowS_deriv a0 β s hs.1).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset self_mem_nhdsWithin (fun u hu => hs.1.trans hu)
  have hc : ∀ β : ℝ, ContinuousOn (flowS a0 β) (Icc 0 T) := fun β s hs =>
    ((flowS_deriv a0 β s hs.1).continuousWithinAt).mono (fun u hu => hu.1)
  have h0 : dist (flowS a0 α 0) (flowS a0 α₀ 0) ≤ |α - α₀| := by
    rw [flowS_zero, flowS_zero]
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

end Work.Suction.F10SFlow
