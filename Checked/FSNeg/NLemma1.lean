import Checked.FalknerSkan.LimitCore
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

/-! Falkner–Skan adverse pressure gradient, elementary sign facts for the scaled adverse-pressure system, with no sign condition on its coefficient. Module `NLemma1`, promoted from `Work/FSNeg/NLemma1.lean`. -/

namespace Checked.FSNeg.NLemma1
open Set Filter Topology
open Checked.FalknerSkan.LimitCore

/-- Lemma 1 (no return to q = 0): if q > 0 on [a, η₁) and p(η₁)² < 1, then q(η₁) > 0. -/
theorem q_pos_at {K : ℝ} {f p q : ℝ → ℝ}
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(K * f η * q η) + 1 - p η ^ 2) (Ici 0) η)
    {a η₁ : ℝ} (ha : 0 ≤ a) (haη : a < η₁) (hpos : ∀ η ∈ Ico a η₁, 0 < q η)
    (hp1 : p η₁ ^ 2 < 1) : 0 < q η₁ := by
  have hη₁ : 0 < η₁ := lt_of_le_of_lt ha haη
  have hd := at_of hq hη₁
  have hge : 0 ≤ q η₁ := by
    refine ge_of_tendsto (hd.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio η₁))) ?_
    filter_upwards [Ioo_mem_nhdsLT haη] with y hy
    exact (hpos y ⟨hy.1.le, hy.2⟩).le
  rcases eq_or_lt_of_le hge with h0 | h0
  · exfalso
    have hdpos : 0 < -(K * f η₁ * q η₁) + 1 - p η₁ ^ 2 := by
      rw [← h0]; linarith
    have hleft := left_neg hd hdpos h0.symm
    obtain ⟨y, hy1, hy2⟩ := (hleft.and (Ioo_mem_nhdsLT haη)).exists
    have := hpos y ⟨hy2.1.le, hy2.2⟩
    linarith
  · exact h0

/-- Lemma 1 on an interval: q(a) > 0 and p² < 1 on (a, b] give q > 0 on [a, b]. -/
theorem q_pos_on {K : ℝ} {f p q : ℝ → ℝ}
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(K * f η * q η) + 1 - p η ^ 2) (Ici 0) η)
    {a b : ℝ} (ha : 0 ≤ a) (hqa : 0 < q a) (hp1 : ∀ η ∈ Ioc a b, p η ^ 2 < 1) :
    ∀ η ∈ Icc a b, 0 < q η := by
  intro t₁ ht₁
  by_contra hneg
  rw [not_lt] at hneg
  set S : Set ℝ := Icc a t₁ ∩ q ⁻¹' Iic 0 with hS
  have hSc : IsClosed S :=
    (cont_of hq ha).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSne : S.Nonempty := ⟨t₁, ⟨ht₁.1, le_refl t₁⟩, hneg⟩
  have hSbdd : BddBelow S := ⟨a, fun t ht => ht.1.1⟩
  have hτ : sInf S ∈ S := hSc.csInf_mem hSne hSbdd
  have hτa : a < sInf S := by
    rcases eq_or_lt_of_le hτ.1.1 with h | h
    · exfalso
      have h2 : q (sInf S) ≤ 0 := hτ.2
      rw [← h] at h2
      linarith
    · exact h
  have hbefore : ∀ t ∈ Ico a (sInf S), 0 < q t := by
    intro t ht
    by_contra hc
    rw [not_lt] at hc
    have htS : t ∈ S := ⟨⟨ht.1, le_trans ht.2.le hτ.1.2⟩, hc⟩
    have := csInf_le hSbdd htS
    linarith [ht.2]
  have := q_pos_at hq ha hτa hbefore (hp1 _ ⟨hτa, le_trans hτ.1.2 ht₁.2⟩)
  have h2 : q (sInf S) ≤ 0 := hτ.2
  linarith

/-- Lemma C (positivity part): a solution with f(0) = 0, p(0) = 0, q(0) ≥ 0 and p² < 1 on
(0, ∞) has q > 0 on (0, ∞). -/
theorem q_pos_of_class {K : ℝ} {f p q : ℝ → ℝ}
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(K * f η * q η) + 1 - p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hq0 : 0 ≤ q 0)
    (hp1 : ∀ η ∈ Ioi (0 : ℝ), p η ^ 2 < 1) :
    ∀ η ∈ Ioi (0 : ℝ), 0 < q η := by
  -- right derivative 1 at 0
  have hd0 : HasDerivWithinAt q 1 (Ici 0) 0 := by
    have := hq 0 (mem_Ici.2 le_rfl)
    rw [hf0, hp0] at this
    simpa using this
  have ht := hasDerivWithinAt_iff_tendsto_slope.1 (hd0.mono Ioi_subset_Ici_self)
  rw [sdiff_singleton_eq_self (by simp)] at ht
  have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), 0 < slope q 0 y := ht.eventually (lt_mem_nhds one_pos)
  intro η hη
  obtain ⟨a, ha1, ha2⟩ := (hev.and (Ioo_mem_nhdsGT (show (0 : ℝ) < η from hη))).exists
  have hqa : 0 < q a := by
    rw [slope_def_field, sub_zero] at ha1
    have hqa' : 0 < q a - q 0 := by
      rcases div_pos_iff.1 ha1 with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact h1
      · linarith [ha2.1]
    linarith
  exact q_pos_on hq ha2.1.le hqa (fun t ht => hp1 t (lt_trans ha2.1 ht.1)) η
    ⟨ha2.2.le, le_refl η⟩

end Checked.FSNeg.NLemma1

