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
import Checked.FSAtt.AAssemble
import Checked.FalknerSkan.NegDecay

/-! Falkner–Skan adverse pressure gradient with a free scaled coefficient at least five: two certified chains (slow approach below, overshoot above) give a fast-approach solution with its wall shear between the two scaled wall values, and the same window for every fast-approach solution. Module `AWindow`, promoted from `Work/FSAtt/AWindow.lean`. -/

namespace Checked.FSAtt.AWindow
open Set Filter Topology Checked.FSNeg.NBase Checked.FSSep.SBase Checked.FSAtt.ABase Checked.FSAtt.AFlow
  Checked.FSAtt.AAssemble

theorem core_window {K : ℝ} (hK5 : 5 ≤ K) {lo hi : ℝ} (hlo0 : 0 < lo) (hlh : lo < hi) (hhi1 : hi ≤ 11 / 10)
    (hS : ChainA K lo SlowA) (hO : ChainA K hi Over) :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / K) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q η) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      lo / Real.sqrt K < q 0 ∧ q 0 < hi / Real.sqrt K := by
  have slow_lo : SlowA (flowA K lo) := of_chain hS
  have over_hi : Over (flowA K hi) := of_chain hO
  set S : Set ℝ := {α | α ∈ Icc lo hi ∧ SlowA (flowA K α)} with hSd
  have hloS : lo ∈ S := ⟨⟨le_rfl, hlh.le⟩, slow_lo⟩
  have hne : S.Nonempty := ⟨lo, hloS⟩
  have hbdd : BddAbove S := ⟨hi, fun α hα => hα.1.2⟩
  set a := sSup S with ha
  have hloa := le_csSup hbdd hloS
  obtain ⟨δ2, hδ2, hO2⟩ := over_open K hi over_hi
  have ha_lt : a < hi := by
    have hub : ∀ α ∈ S, α ≤ hi - δ2 / 2 := by
      intro α hα
      by_contra hc
      push Not at hc
      have hOα := hO2 α (by rw [abs_lt]; constructor <;> linarith [hα.1.2])
      exact slow_not_over hK5 (by linarith [hα.1.1]) (by linarith [hα.1.2]) hα.2 hOα
    have := csSup_le hne hub
    linarith
  have hnS : ¬ SlowA (flowA K a) := by
    intro hSa
    obtain ⟨δ, hδ, hSa'⟩ := slow_open K a hSa
    obtain ⟨α', hα'd⟩ : ∃ x : ℝ, x = a + min (δ / 2) ((hi - a) / 2) := ⟨_, rfl⟩
    have h1 : 0 < min (δ / 2) ((hi - a) / 2) := lt_min (by linarith) (by linarith)
    have h2 : min (δ / 2) ((hi - a) / 2) ≤ δ / 2 := min_le_left _ _
    have h3 : min (δ / 2) ((hi - a) / 2) ≤ (hi - a) / 2 := min_le_right _ _
    have hα'S : α' ∈ S := ⟨⟨by linarith, by linarith⟩,
      hSa' α' (by rw [abs_lt]; constructor <;> linarith)⟩
    have := le_csSup hbdd hα'S
    linarith
  have hnO : ¬ Over (flowA K a) := by
    intro hOa
    obtain ⟨δ, hδ, hOa'⟩ := over_open K a hOa
    obtain ⟨α, hαS, hαa⟩ := exists_lt_of_lt_csSup hne (show a - δ < a by linarith)
    have hle : α ≤ a := le_csSup hbdd hαS
    exact slow_not_over hK5 (by linarith [hαS.1.1]) (by linarith [hαS.1.2]) hαS.2
      (hOa' α (by rw [abs_lt]; constructor <;> linarith))
  have hlo_lt : lo < a := by
    rcases eq_or_lt_of_le hloa with h | h
    · exact absurd (by rw [ha, ← h]; exact slow_lo) hnS
    · exact h
  obtain ⟨tF, tP, tQ, hlim, hqpos, hdec⟩ :=
    neither_class hK5 (by linarith) (by linarith) hnS hnO
  set F := fun t => (flowA K a t).1
  set P := fun t => (flowA K a t).2.1
  set Q := fun t => (flowA K a t).2.2
  have hF0 : F 0 = 0 := by simp [F, flowA_zero]
  have hP0 : P 0 = 0 := by simp [P, flowA_zero]
  have hQ0 : Q 0 = a := by simp [Q, flowA_zero]
  have hc : 0 < Real.sqrt K := Real.sqrt_pos.2 (by linarith)
  have hc2 : Real.sqrt K ^ 2 = K := Real.sq_sqrt (by linarith)
  have tQ' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(K * F η * Q η) - (-1) * (1 - P η ^ 2)) (Ici 0) η :=
    fun η hη => (tQ η hη).congr_deriv (by ring)
  obtain ⟨A, B, C⟩ := Checked.FalknerSkan.FSScale.scale hc tF tP tQ'
  have hm := Checked.FalknerSkan.FSScale.mapsTo_div hc
  refine ⟨fun s => Real.sqrt K * F (s / Real.sqrt K), fun s => P (s / Real.sqrt K),
    fun s => Q (s / Real.sqrt K) / Real.sqrt K, A, B, fun s hs => ?_, by simp [hF0],
    by simp [hP0], Checked.FalknerSkan.FSScale.scale_lim hc hlim,
    fun s hs => div_pos (hqpos _ (hm hs)) hc, fun M => ?_, ?_, ?_⟩
  · refine (C s hs).congr_deriv ?_
    field_simp
    rw [hc2]
  · have hd := (tendsto_id.atTop_div_const hc).eventually (hdec (M * Real.sqrt K))
    filter_upwards [hd] with s hs
    simp only [id] at hs
    rw [le_div_iff₀ hc]
    linarith
  · simp only [zero_div, hQ0]
    exact div_lt_div_of_pos_right hlo_lt hc
  · simp only [zero_div, hQ0]
    exact div_lt_div_of_pos_right ha_lt hc

/-- The window from two certified chains, for every decay-class solution (uniqueness from
`Checked.FalknerSkan.NegDecay.fs_neg_decay_equal`). -/
theorem window_of_chains {K : ℝ} (hK5 : 5 ≤ K) {lo hi : ℝ} (hlo0 : 0 < lo) (hlh : lo < hi)
    (hhi1 : hi ≤ 11 / 10) (hS : ChainA K lo SlowA) (hO : ChainA K hi Over) (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / K) * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :
    lo / Real.sqrt K < q 0 ∧ q 0 < hi / Real.sqrt K := by
  obtain ⟨f₁, p₁, q₁, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ :=
    core_window hK5 hlo0 hlh hhi1 hS hO
  have hβ : -1 / K < 0 := div_neg_of_neg_of_pos (by norm_num) (by linarith)
  have E := Checked.FalknerSkan.NegDecay.fs_neg_decay_equal (-1 / K) hβ f p q f₁ p₁ q₁
    hf hp hq hf0 hp0 hlim hpos hdec a1 a2 a3 a4 a5 a6 a7 a8 0 (le_refl (0 : ℝ))
  rw [E.2.2]
  exact ⟨w1, w2⟩

end Checked.FSAtt.AWindow
