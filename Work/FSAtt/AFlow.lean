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
import Checked.FSSep.SFlow

/-! Falkner–Skan adverse pressure gradient with a free coefficient K: the global flow of the clamped field
`vS K` from (0, 0, α), continuous in the wall value α (port of `Checked/FSNeg/NFlow.lean` to the coefficient-K
field of `Checked/FSSep/SBase.lean`; Lipschitz bound, norm bound and uniqueness from `Checked/FSSep/SFlow.lean`).
Run 2026-11-11T1028Z. -/

namespace Work.FSAtt.AFlow
open Set Checked.FSNeg.NBase Checked.FSSep.SBase Checked.FSSep.SFlow

theorem local_sol (K α T : ℝ) (hT : 0 < T) : ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = (0, 0, α) ∧
    ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vS K t (Y t)) (Icc 0 T) t := by
  set L : ℝ := 2 * |K| * T + 4 * |K| + 5 with hL
  have hL0 : 0 ≤ L := by positivity
  have hPL : IsPicardLindelof (vS K) (tmin := 0) (tmax := T) ⟨0, le_rfl, hT.le⟩
      ((0 : ℝ), (0 : ℝ), α) (Real.toNNReal (L * T)) 0 (Real.toNNReal L)
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

theorem exists_sol (K α : ℝ) : ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = (0, 0, α) ∧
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt Y (vS K t (Y t)) (Ici 0) t := by
  have hex : ∀ n : ℕ, ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = (0, 0, α) ∧
      ∀ t ∈ Icc 0 ((n : ℝ) + 1), HasDerivWithinAt Y (vS K t (Y t)) (Icc 0 ((n : ℝ) + 1)) t :=
    fun n => local_sol K α _ (by positivity)
  choose sol hsol0 hsol using hex
  have hag : ∀ k n : ℕ, ∀ s ∈ Icc (0 : ℝ) ((k : ℝ) + 1), s ≤ (n : ℝ) + 1 → sol k s = sol n s := by
    intro k n s hs hsn
    rcases le_total k n with hkn | hnk
    · have hkn' : (k : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hkn 1
      exact Checked.FSSep.SFlow.unique_right (by positivity) (hsol k)
        (fun t ht => (hsol n t ⟨ht.1, ht.2.trans hkn'⟩).mono (Icc_subset_Icc_right hkn'))
        ((hsol0 k).trans (hsol0 n).symm) hs
    · have hnk' : (n : ℝ) + 1 ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnk 1
      exact (Checked.FSSep.SFlow.unique_right (by positivity) (hsol n)
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
noncomputable def flowA (K α : ℝ) : ℝ → ℝ × ℝ × ℝ := Classical.choose (exists_sol K α)

theorem flowA_zero (K α : ℝ) : flowA K α 0 = (0, 0, α) := (Classical.choose_spec (exists_sol K α)).1

theorem flowA_deriv (K α : ℝ) :
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (flowA K α) (vS K t (flowA K α t)) (Ici 0) t :=
  (Classical.choose_spec (exists_sol K α)).2

/-- Continuity of the flow in α, uniformly on [0, T]. -/
theorem flowA_cont (K T : ℝ) (hT : 0 ≤ T) (α₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ α, |α - α₀| < δ → ∀ t ∈ Icc 0 T, dist (flowA K α t) (flowA K α₀ t) < ε := by
  set L : ℝ := |K| * T + 4 * |K| + 4 with hL
  set E : ℝ := Real.exp (L * T) with hE
  have hE0 : 0 < E := Real.exp_pos _
  refine ⟨ε / E, div_pos hε hE0, fun α hα t ht => ?_⟩
  have hd : ∀ (β : ℝ), ∀ s ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt (flowA K β) (vS K s (flowA K β s)) (Ici s) s := by
    intro β s hs
    refine (flowA_deriv K β s hs.1).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset self_mem_nhdsWithin (fun u hu => hs.1.trans hu)
  have hc : ∀ β : ℝ, ContinuousOn (flowA K β) (Icc 0 T) := fun β s hs =>
    ((flowA_deriv K β s hs.1).continuousWithinAt).mono (fun u hu => hu.1)
  have h0 : dist (flowA K α 0) (flowA K α₀ 0) ≤ |α - α₀| := by
    rw [flowA_zero, flowA_zero]
    simp [Prod.dist_eq, Real.dist_eq]
  have key := dist_le_of_trajectories_ODE_of_mem (v := vS K) (s := fun _ => univ)
    (K := Real.toNNReal L) (fun s hs => (lip K (Ico_subset_Icc_self hs)).lipschitzOnWith)
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

end Work.FSAtt.AFlow
