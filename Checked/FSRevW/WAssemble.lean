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
import Checked.FSNeg.NUnclamp
import Checked.FSNeg.NLimit
import Checked.FSNeg.NRiccati
import Checked.FSAtt.AAssemble
import Checked.FSRev.RBase
import Checked.FSRevW.WFlow
import Checked.FSRevW.WInv
import Checked.FSRevW.WUnclamp
import Checked.FalknerSkan.FSScale

/-! Falkner–Skan adverse pressure gradient with a free scaled coefficient at least five and a shear clamp level at least two, the shooting argument of the reversed-flow branch with a tube of free end time (at least one): an overshoot chain below, a slow-approach chain above and a tube give a reversed-flow solution in the fast-approach class with its wall value between the two scaled wall values. Ported from `Checked/FSRev/RAssemble.lean` and `Checked/FSRev/RAssembleA.lean` by `runs/2026-11-13T0628Z/scripts/port_wrest.py`. Module `WAssemble`, run 2026-11-13T0628Z. -/

namespace Checked.FSRevW.WAssemble
open Set Filter Topology Checked.FSNeg.NBase Checked.FSSep.SBase Checked.FSRev.RBase Checked.FalknerSkan.LimitCore
  Checked.FSRevW.WBase Checked.FSRevW.WFlow

theorem slowR_open (Cq K α₀ : ℝ) (h : SlowR (flowW Cq K α₀)) :
    ∃ δ > 0, ∀ α, |α - α₀| < δ → SlowR (flowW Cq K α) := by
  obtain ⟨η, hη, hpre, h1, h2, h3, h4⟩ := h
  have hη0 : (0 : ℝ) ≤ η := by linarith
  have hcp : ContinuousOn (fun s => (flowW Cq K α₀ s).2.1) (Icc 0 η) :=
    (continuous_fst.comp continuous_snd).comp_continuousOn (cont_comp Cq K α₀ η)
  obtain ⟨s1, hs1, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, ⟨le_rfl, hη0⟩⟩ hcp
  have hM : (flowW Cq K α₀ s1).2.1 < 1 := hpre s1 hs1
  set ε := min (min (1 - (flowW Cq K α₀ s1).2.1) ((flowW Cq K α₀ η).2.1 - 1 / 3))
    (min ((flowW Cq K α₀ η).2.2) (min ((3 * (1 - (flowW Cq K α₀ η).2.1) - (flowW Cq K α₀ η).2.2) / 4)
      ((flowW Cq K α₀ η).1 - 11 / 15))) with hε
  have e1 : ε ≤ 1 - (flowW Cq K α₀ s1).2.1 := (min_le_left _ _).trans (min_le_left _ _)
  have e2 : ε ≤ (flowW Cq K α₀ η).2.1 - 1 / 3 := (min_le_left _ _).trans (min_le_right _ _)
  have e3 : ε ≤ (flowW Cq K α₀ η).2.2 := (min_le_right _ _).trans (min_le_left _ _)
  have e4 : ε ≤ (3 * (1 - (flowW Cq K α₀ η).2.1) - (flowW Cq K α₀ η).2.2) / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have e5 : ε ≤ (flowW Cq K α₀ η).1 - 11 / 15 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hε0 : 0 < ε := lt_min (lt_min (by linarith) (by linarith))
    (lt_min h2 (lt_min (by linarith) (by linarith)))
  obtain ⟨δ, hδ, hcl⟩ := flowW_cont Cq K η hη0 α₀ hε0
  refine ⟨δ, hδ, fun α hα => ⟨η, hη, fun s hs => ?_, ?_, ?_, ?_, ?_⟩⟩
  · have k1 := (Checked.FSAtt.AAssemble.dist_c1 (a := flowW Cq K α s) (b := flowW Cq K α₀ s)).trans_lt (hcl α hα s hs)
    have := hmax hs
    simp only [mem_ofPred_eq] at this
    rw [abs_lt] at k1; linarith
  all_goals
    have k := hcl α hα η ⟨hη0, le_rfl⟩
    have k0 := (Checked.FSAtt.AAssemble.dist_c0 (a := flowW Cq K α η) (b := flowW Cq K α₀ η)).trans_lt k
    have k1 := (Checked.FSAtt.AAssemble.dist_c1 (a := flowW Cq K α η) (b := flowW Cq K α₀ η)).trans_lt k
    have k2 := (Checked.FSAtt.AAssemble.dist_c2 (a := flowW Cq K α η) (b := flowW Cq K α₀ η)).trans_lt k
    rw [abs_lt] at k0 k1 k2
  · linarith
  · linarith
  · linarith
  · linarith

theorem slowR_not_over {Cq K : ℝ} (hC : 2 ≤ Cq) (hK5 : 5 ≤ K) {α : ℝ} (hS : SlowR (flowW Cq K α)) (hO : Over (flowW Cq K α)) : False := by
  obtain ⟨hF, hP, hQ⟩ := comps Cq K α
  obtain ⟨η, hη, hpre, h1, h2, h3, h4⟩ := hS
  have hη0 : (0 : ℝ) ≤ η := by linarith
  -- f η ≤ η: t − f t is nondecreasing on [0, η] (f' = cl 2 p ≤ 1 there)
  have hgm : MonotoneOn (fun s => s - (flowW Cq K α s).1) (Icc 0 η) :=
    mono (g' := fun s => 1 - cl 2 (flowW Cq K α s).2.1)
      (fun x hx => ((hasDerivWithinAt_id x (Ici 0)).sub (hF x hx))) le_rfl (fun x hx => by
        have := hpre x ⟨hx.1.le, hx.2.le⟩
        have : cl 2 (flowW Cq K α x).2.1 ≤ 1 := by
          unfold cl; exact max_le (by norm_num) ((min_le_right _ _).trans this.le)
        linarith)
  have hfη : (flowW Cq K α η).1 ≤ η + 1 := by
    have := hgm ⟨le_rfl, hη0⟩ ⟨hη0, le_rfl⟩ hη0
    simp only [flowW_zero] at this; linarith
  have I := Checked.FSRevW.WInv.slow_inv_clW hC hK5 hF hP hQ hη0 h1
    (by have := hpre η ⟨hη0, le_rfl⟩; exact this) h2 h3 h4 hfη
  obtain ⟨η', hη', hp⟩ := hO
  rcases le_total η' η with h | h
  · linarith [hpre η' ⟨hη'.le, h⟩]
  · linarith [(I η' h).2.1]

/-- The touch lemma for the clamped flow: p = 1 and q = 0 together at τ > 0 is impossible. -/
theorem no_touch {Cq : ℝ} (hC : 2 ≤ Cq) (K α : ℝ) : ∀ τ, 0 < τ → (flowW Cq K α τ).2.1 = 1 → (flowW Cq K α τ).2.2 = 0 → False := by
  intro τ hτ hpτ hqτ
  set Z : ℝ → ℝ × ℝ × ℝ := fun t => ((flowW Cq K α τ).1 + (t - τ), 1, 0) with hZ
  have hZd : ∀ t ∈ Icc 0 τ, HasDerivWithinAt Z (vW Cq K t (Z t)) (Icc 0 τ) t := by
    intro t _
    have hv : vW Cq K t (Z t) = (1, 0, 0) := by
      simp only [hZ, vW]
      rw [Checked.FSNeg.NUnclamp.cl_eq (c := 2) (y := 1) (by norm_num) (by norm_num),
        Checked.FSNeg.NUnclamp.cl_eq (c := Cq) (y := 0) (by linarith) (by linarith)]
      simp
    rw [hv]
    have a1 : HasDerivWithinAt (fun t => (flowW Cq K α τ).1 + (t - τ)) 1 (Icc 0 τ) t :=
      ((hasDerivWithinAt_id t _).sub_const τ).const_add _ |>.congr_deriv (by simp)
    exact a1.prodMk ((hasDerivWithinAt_const t _ (1 : ℝ)).prodMk (hasDerivWithinAt_const t _ (0 : ℝ)))
  have hY : ∀ t ∈ Icc 0 τ, HasDerivWithinAt (flowW Cq K α) (vW Cq K t (flowW Cq K α t)) (Icc 0 τ) t :=
    fun t ht => (flowW_deriv Cq K α t ht.1).mono (fun x hx => hx.1)
  have hZτ : flowW Cq K α τ = Z τ := by
    simp only [hZ, sub_self, add_zero]
    ext
    · rfl
    · exact hpτ
    · exact hqτ
  have := Checked.FSRevW.WFlow.unique_left hτ.le hY hZd hZτ (⟨le_rfl, hτ.le⟩ : (0 : ℝ) ∈ Icc 0 τ)
  have h2 := congrArg (fun y => y.2.1) this
  simp only [hZ, flowW_zero] at h2
  norm_num at h2

theorem tube_flowW {Cq K lo hi L α : ℝ} (hT : TubeW Cq K lo hi L) (hα : α ∈ Icc lo hi) :
    (∀ t ∈ Icc (0 : ℝ) L, PhiW Cq (fun t => (flowW Cq K α t).1) (fun t => (flowW Cq K α t).2.1)
      (fun t => (flowW Cq K α t).2.2) t) ∧
    (0 < (flowW Cq K α L).1 ∧ (flowW Cq K α L).1 < 1 ∧ 0 < (flowW Cq K α L).2.1 ∧
      (flowW Cq K α L).2.1 < 1 ∧ 0 < (flowW Cq K α L).2.2 ∧ (flowW Cq K α L).2.2 < 6 / 5) :=
  hT α hα (flowW Cq K α) (fun t ht => (flowW_deriv Cq K α t ht.1).mono Icc_subset_Ici_self) (flowW_zero Cq K α)

/-- Neither event, inside the tube: the flow solves the scaled problem with −1/2 < p < 1, p → 1
and the faster-than-every-exponential approach. -/
theorem neither_classRW {Cq K : ℝ} (hC : 2 ≤ Cq) (hK5 : 5 ≤ K) {L : ℝ} (hL : 1 ≤ L) {lo hi α : ℝ} (hT : TubeW Cq K lo hi L) (hα : α ∈ Icc lo hi)
    (hnS : ¬ SlowR (flowW Cq K α)) (hnO : ¬ Over (flowW Cq K α)) :
    let F := fun t => (flowW Cq K α t).1
    let P := fun t => (flowW Cq K α t).2.1
    let Q := fun t => (flowW Cq K α t).2.2
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt F (P η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt P (Q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(K * F η * Q η) + 1 - P η ^ 2) (Ici 0) η) ∧
    Tendsto P atTop (𝓝 1) ∧ (∀ η ∈ Ici (0 : ℝ), -1 / 2 < P η ∧ P η < 1) ∧
    (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - P η) ≤ Q η) := by
  intro F P Q
  obtain ⟨hF, hP, hQ⟩ := comps Cq K α
  have h0 := flowW_zero Cq K α
  have hP0 : P 0 = 0 := by simp [P, h0]
  obtain ⟨tube, e1, e2, e3, e4, e5, e6⟩ := tube_flowW hT hα
  have hp1 : ∀ t ∈ Ici (0 : ℝ), P t ≤ 1 := by
    intro t ht
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ t from ht) with h | h
    · rw [← h, hP0]; norm_num
    · by_contra hc; push Not at hc; exact hnO ⟨t, h, hc⟩
  have U := Checked.FSRevW.WUnclamp.unclamp_fromW hC (by linarith) (a := L) hL hF hP hQ e1 e2 e3 e4 e5 e6
    (fun t ht => hp1 t (le_trans (by linarith : (0 : ℝ) ≤ L) ht)) (fun τ hτ => no_touch hC K α τ (by linarith))
  -- inside the clamps everywhere
  have box : ∀ η ∈ Ici (0 : ℝ), |F η| ≤ η + 2 ∧ |P η| ≤ 2 ∧ |Q η| ≤ Cq := by
    intro η hη
    have hη0 : (0 : ℝ) ≤ η := hη
    rcases le_total η L with h | h
    · exact (tube η ⟨hη0, h⟩).1
    · obtain ⟨u1, u2, u3, u4, u5, u6⟩ := U η h
      exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩,
        abs_le.2 ⟨by linarith, by linarith⟩⟩
  have ceq : ∀ {c y : ℝ}, |y| ≤ c → cl c y = y := fun h => cl_of_abs_le h
  have tF : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt F (P η) (Ici 0) η := fun η hη => by
    have := hF η hη; rwa [ceq (box η hη).2.1] at this
  have tP : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt P (Q η) (Ici 0) η := fun η hη => by
    have := hP η hη; rwa [ceq (box η hη).2.2] at this
  have tQ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(K * F η * Q η) + 1 - P η ^ 2) (Ici 0) η :=
    fun η hη => by
    have hη0 : (0 : ℝ) ≤ η := hη
    have := hQ η hη
    rwa [ceq (c := max η 0 + 2) (y := F η) (by rw [max_eq_left hη0]; exact (box η hη).1),
      ceq (box η hη).2.2, ceq (box η hη).2.1] at this
  -- p < 1: an interior maximum p = 1 would force q = 0 (touch)
  have hplt : ∀ η ∈ Ici (0 : ℝ), P η < 1 := by
    intro η hη
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ η from hη) with h | h
    · rw [← h, hP0]; norm_num
    · rcases lt_or_eq_of_le (hp1 η hη) with h1 | h1
      · exact h1
      · exfalso
        have hd := at_of tP h
        have hmax : IsLocalMax P η := by
          filter_upwards [Ici_mem_nhds h] with x hx
          rw [h1]; exact hp1 x hx
        exact no_touch hC K α η h h1 (hmax.hasDerivAt_eq_zero hd)
  have hpgt : ∀ η ∈ Ici (0 : ℝ), -1 / 2 < P η := by
    intro η hη
    rcases le_total η L with h | h
    · exact (tube η ⟨hη, h⟩).2
    · linarith [(U η h).1]
  have hqpos : ∀ η ∈ Ici L, 0 < Q η := fun η hη => (U η hη).2.2.1
  have hlim : Tendsto P atTop (𝓝 1) :=
    Checked.FSNeg.NLimit.neg_limit (by linarith : (0 : ℝ) < K) tF tP tQ (by linarith : (0 : ℝ) ≤ L)
      hqpos (by linarith) (fun η hη => hplt η (le_trans (by linarith : (0 : ℝ) ≤ L) hη))
  have hft := Checked.FSNeg.NLimit.f_tendsto tF hlim
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hft.eventually_gt_atTop (11 / 15))
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 (hlim.eventually (lt_mem_nhds (show (1 : ℝ) / 3 < 1 by norm_num)))
  set a := max (max N N2) (max 2 L) with ha
  have ha2 : (2 : ℝ) ≤ a := le_trans (le_max_left _ _) (le_max_right _ _)
  have haL : L ≤ a := le_trans (le_max_right _ _) (le_max_right _ _)
  have ha0 : (0 : ℝ) ≤ a := le_trans (by norm_num) ha2
  have hlow : ∀ η ∈ Ici a, 3 * (1 - P η) ≤ Q η := by
    intro η hη
    have hη' : a ≤ η := hη
    by_contra hc
    push Not at hc
    apply hnS
    refine ⟨η, by linarith, fun s hs => hplt s hs.1,
      hN2 η ((le_max_right N N2).trans ((le_max_left _ _).trans hη')),
      hqpos η (show L ≤ η by linarith), hc,
      hN η ((le_max_left N N2).trans ((le_max_left _ _).trans hη'))⟩
  refine ⟨tF, tP, tQ, hlim, fun η hη => ⟨hpgt η hη, hplt η hη⟩, ?_⟩
  exact Checked.FSNeg.NRiccati.riccati_up (by linarith : (0 : ℝ) < K) (by norm_num : (0 : ℝ) < 3)
    tP tQ ha0 (fun η hη => hplt η (ha0.trans hη)) hft hlow

theorem core_revW {Cq K : ℝ} (hC : 2 ≤ Cq) (hK5 : 5 ≤ K) {L : ℝ} (hL : 1 ≤ L) {lo hi : ℝ} (hlh : lo < hi)
    (hO : ChainW Cq K lo Over) (hS : ChainW Cq K hi SlowR) (hT : TubeW Cq K lo hi L) :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / K) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 / 2 < p η ∧ p η < 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      lo / Real.sqrt K < q 0 ∧ q 0 < hi / Real.sqrt K := by
  have over_lo : Over (flowW Cq K lo) := of_chain hO
  have slow_hi : SlowR (flowW Cq K hi) := of_chain hS
  set S : Set ℝ := {α | α ∈ Icc lo hi ∧ Over (flowW Cq K α)} with hSd
  have hloS : lo ∈ S := ⟨⟨le_rfl, hlh.le⟩, over_lo⟩
  have hne : S.Nonempty := ⟨lo, hloS⟩
  have hbdd : BddAbove S := ⟨hi, fun α hα => hα.1.2⟩
  set a := sSup S with ha
  have hloa := le_csSup hbdd hloS
  obtain ⟨δ2, hδ2, hS2⟩ := slowR_open Cq K hi slow_hi
  have ha_lt : a < hi := by
    have hub : ∀ α ∈ S, α ≤ hi - δ2 / 2 := by
      intro α hα
      by_contra hc
      push Not at hc
      exact slowR_not_over hC hK5 (hS2 α (by rw [abs_lt]; constructor <;> linarith [hα.1.2])) hα.2
    have := csSup_le hne hub
    linarith
  have hnO : ¬ Over (flowW Cq K a) := by
    intro hOa
    obtain ⟨δ, hδ, hOa'⟩ := over_open Cq K a hOa
    obtain ⟨α', hα'd⟩ : ∃ x : ℝ, x = a + min (δ / 2) ((hi - a) / 2) := ⟨_, rfl⟩
    have h1 : 0 < min (δ / 2) ((hi - a) / 2) := lt_min (by linarith) (by linarith)
    have h2 : min (δ / 2) ((hi - a) / 2) ≤ δ / 2 := min_le_left _ _
    have h3 : min (δ / 2) ((hi - a) / 2) ≤ (hi - a) / 2 := min_le_right _ _
    have hα'S : α' ∈ S := ⟨⟨by linarith, by linarith⟩,
      hOa' α' (by rw [abs_lt]; constructor <;> linarith)⟩
    have := le_csSup hbdd hα'S
    linarith
  have hnS : ¬ SlowR (flowW Cq K a) := by
    intro hSa
    obtain ⟨δ, hδ, hSa'⟩ := slowR_open Cq K a hSa
    obtain ⟨α, hαS, hαa⟩ := exists_lt_of_lt_csSup hne (show a - δ < a by linarith)
    have hle : α ≤ a := le_csSup hbdd hαS
    exact slowR_not_over hC hK5 (hSa' α (by rw [abs_lt]; constructor <;> linarith)) hαS.2
  have hlo_lt : lo < a := by
    rcases eq_or_lt_of_le hloa with h | h
    · exact absurd (by rw [ha, ← h]; exact over_lo) hnO
    · exact h
  obtain ⟨tF, tP, tQ, hlim, hpb, hdec⟩ :=
    neither_classRW hC hK5 hL hT ⟨hloa, ha_lt.le⟩ hnS hnO
  set F := fun t => (flowW Cq K a t).1
  set P := fun t => (flowW Cq K a t).2.1
  set Q := fun t => (flowW Cq K a t).2.2
  have hF0 : F 0 = 0 := by simp [F, flowW_zero]
  have hP0 : P 0 = 0 := by simp [P, flowW_zero]
  have hQ0 : Q 0 = a := by simp [Q, flowW_zero]
  have hc : 0 < Real.sqrt K := Real.sqrt_pos.2 (by linarith)
  have hc2 : Real.sqrt K ^ 2 = K := Real.sq_sqrt (by linarith)
  have tQ' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(K * F η * Q η) - (-1) * (1 - P η ^ 2)) (Ici 0) η :=
    fun η hη => (tQ η hη).congr_deriv (by ring)
  obtain ⟨A, B, C⟩ := Checked.FalknerSkan.FSScale.scale hc tF tP tQ'
  have hm := Checked.FalknerSkan.FSScale.mapsTo_div hc
  refine ⟨fun s => Real.sqrt K * F (s / Real.sqrt K), fun s => P (s / Real.sqrt K),
    fun s => Q (s / Real.sqrt K) / Real.sqrt K, A, B, fun s hs => ?_, by simp [hF0],
    by simp [hP0], Checked.FalknerSkan.FSScale.scale_lim hc hlim,
    fun s hs => hpb _ (hm hs), fun M => ?_, ?_, ?_⟩
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

end Checked.FSRevW.WAssemble
