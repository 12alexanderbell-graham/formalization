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
import Checked.FSNeg.NAssemble
import Checked.FSNeg.LCell
import Checked.FSNeg.LInv
import Checked.FSNeg.LUnclamp
import Checked.FalknerSkan.FSScale

/-! Falkner–Skan adverse pressure gradient, the shooting argument on the reversed-flow branch: openness and disjointness of the two event sets, a wall value in neither, and the solution it gives. Module `LAssemble`, promoted from `Work/FSNeg/LAssemble.lean`. -/

namespace Checked.FSNeg.LAssemble
open Set Filter Topology Checked.FSNeg.NBase Checked.FSNeg.NFlow Checked.FSNeg.NAssemble Checked.FSNeg.LCell
  Checked.FalknerSkan.LimitCore

/-- The certified tube shape: every solution of the clamped field on [0, 3/2] from (0, 0, α),
α ∈ [lo, hi], stays inside the clamps with p > −1/2 and ends in 0 < f < 1, 0 < p < 1,
0 < q < 6/5. -/
def TubeTo (lo hi : ℝ) : Prop :=
  ∀ α ∈ Icc lo hi, ∀ Y : ℝ → ℝ × ℝ × ℝ,
    (∀ t ∈ Icc (0 : ℝ) (3 / 2), HasDerivWithinAt Y (vN t (Y t)) (Icc 0 (3 / 2)) t) →
    Y 0 = (0, 0, α) →
    (∀ t ∈ Icc (0 : ℝ) (3 / 2), PhiT (fun t => (Y t).1) (fun t => (Y t).2.1) (fun t => (Y t).2.2) t) ∧
    (0 < (Y (3 / 2)).1 ∧ (Y (3 / 2)).1 < 1 ∧ 0 < (Y (3 / 2)).2.1 ∧ (Y (3 / 2)).2.1 < 1 ∧
      0 < (Y (3 / 2)).2.2 ∧ (Y (3 / 2)).2.2 < 6 / 5)

theorem slowL_open (α₀ : ℝ) (h : SlowL (flow α₀)) :
    ∃ δ > 0, ∀ α, |α - α₀| < δ → SlowL (flow α) := by
  obtain ⟨η, hη, hpre, h1, h2, h3, h4⟩ := h
  have hη0 : (0 : ℝ) ≤ η := by linarith
  have hcp : ContinuousOn (fun s => (flow α₀ s).2.1) (Icc 0 η) :=
    (continuous_fst.comp continuous_snd).comp_continuousOn (cont_comp α₀ η)
  obtain ⟨s1, hs1, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, ⟨le_rfl, hη0⟩⟩ hcp
  have hM : (flow α₀ s1).2.1 < 1 := hpre s1 hs1
  set ε := min (min (1 - (flow α₀ s1).2.1) ((flow α₀ η).2.1 - 1 / 3))
    (min ((flow α₀ η).2.2) (min ((3 * (1 - (flow α₀ η).2.1) - (flow α₀ η).2.2) / 4)
      ((flow α₀ η).1 - 11 / 30))) with hε
  have e1 : ε ≤ 1 - (flow α₀ s1).2.1 := (min_le_left _ _).trans (min_le_left _ _)
  have e2 : ε ≤ (flow α₀ η).2.1 - 1 / 3 := (min_le_left _ _).trans (min_le_right _ _)
  have e3 : ε ≤ (flow α₀ η).2.2 := (min_le_right _ _).trans (min_le_left _ _)
  have e4 : ε ≤ (3 * (1 - (flow α₀ η).2.1) - (flow α₀ η).2.2) / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have e5 : ε ≤ (flow α₀ η).1 - 11 / 30 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hε0 : 0 < ε := lt_min (lt_min (by linarith) (by linarith))
    (lt_min h2 (lt_min (by linarith) (by linarith)))
  obtain ⟨δ, hδ, hcl⟩ := flow_cont η hη0 α₀ hε0
  refine ⟨δ, hδ, fun α hα => ⟨η, hη, fun s hs => ?_, ?_, ?_, ?_, ?_⟩⟩
  · have k1 := (dist_c1 (a := flow α s) (b := flow α₀ s)).trans_lt (hcl α hα s hs)
    have := hmax hs
    simp only [mem_ofPred_eq] at this
    rw [abs_lt] at k1; linarith
  all_goals
    have k := hcl α hα η ⟨hη0, le_rfl⟩
    have k0 := (dist_c0 (a := flow α η) (b := flow α₀ η)).trans_lt k
    have k1 := (dist_c1 (a := flow α η) (b := flow α₀ η)).trans_lt k
    have k2 := (dist_c2 (a := flow α η) (b := flow α₀ η)).trans_lt k
    rw [abs_lt] at k0 k1 k2
  · linarith
  · linarith
  · linarith
  · linarith

theorem slowL_not_over {α : ℝ} (hS : SlowL (flow α)) (hO : Over (flow α)) : False := by
  obtain ⟨hF, hP, hQ⟩ := comps α
  obtain ⟨η, hη, hpre, h1, h2, h3, h4⟩ := hS
  have hη0 : (0 : ℝ) ≤ η := by linarith
  -- f η ≤ η: t − f t is nondecreasing on [0, η] (f' = cl 2 p ≤ 1 there)
  have hgm : MonotoneOn (fun s => s - (flow α s).1) (Icc 0 η) :=
    mono (g' := fun s => 1 - cl 2 (flow α s).2.1)
      (fun x hx => ((hasDerivWithinAt_id x (Ici 0)).sub (hF x hx))) le_rfl (fun x hx => by
        have := hpre x ⟨hx.1.le, hx.2.le⟩
        have : cl 2 (flow α x).2.1 ≤ 1 := by
          unfold cl; exact max_le (by norm_num) ((min_le_right _ _).trans this.le)
        linarith)
  have hfη : (flow α η).1 ≤ η + 1 := by
    have := hgm ⟨le_rfl, hη0⟩ ⟨hη0, le_rfl⟩ hη0
    simp only [flow_zero] at this; linarith
  have I := Checked.FSNeg.LInv.slow_inv_cl hF hP hQ hη0 h1
    (by have := hpre η ⟨hη0, le_rfl⟩; exact this) h2 h3 h4 hfη
  obtain ⟨η', hη', hp⟩ := hO
  rcases le_total η' η with h | h
  · linarith [hpre η' ⟨hη'.le, h⟩]
  · linarith [(I η' h).2.1]

/-- The touch lemma for the clamped flow: p = 1 and q = 0 together at τ > 0 is impossible. -/
theorem no_touch (α : ℝ) : ∀ τ, 0 < τ → (flow α τ).2.1 = 1 → (flow α τ).2.2 = 0 → False := by
  intro τ hτ hpτ hqτ
  set Z : ℝ → ℝ × ℝ × ℝ := fun t => ((flow α τ).1 + (t - τ), 1, 0) with hZ
  have hZd : ∀ t ∈ Icc 0 τ, HasDerivWithinAt Z (vN t (Z t)) (Icc 0 τ) t := by
    intro t _
    have hv : vN t (Z t) = (1, 0, 0) := by
      simp only [hZ, vN]
      rw [Checked.FSNeg.NUnclamp.cl_eq (c := 2) (y := 1) (by norm_num) (by norm_num),
        Checked.FSNeg.NUnclamp.cl_eq (c := 2) (y := 0) (by norm_num) (by norm_num)]
      simp
    rw [hv]
    have a1 : HasDerivWithinAt (fun t => (flow α τ).1 + (t - τ)) 1 (Icc 0 τ) t :=
      ((hasDerivWithinAt_id t _).sub_const τ).const_add _ |>.congr_deriv (by simp)
    exact a1.prodMk ((hasDerivWithinAt_const t _ (1 : ℝ)).prodMk (hasDerivWithinAt_const t _ (0 : ℝ)))
  have hY : ∀ t ∈ Icc 0 τ, HasDerivWithinAt (flow α) (vN t (flow α t)) (Icc 0 τ) t :=
    fun t ht => (flow_deriv α t ht.1).mono (fun x hx => hx.1)
  have hZτ : flow α τ = Z τ := by
    simp only [hZ, sub_self, add_zero]
    ext
    · rfl
    · exact hpτ
    · exact hqτ
  have := unique_left hτ.le hY hZd hZτ (⟨le_rfl, hτ.le⟩ : (0 : ℝ) ∈ Icc 0 τ)
  have h2 := congrArg (fun y => y.2.1) this
  simp only [hZ, flow_zero] at h2
  norm_num at h2

theorem tube_flow {lo hi α : ℝ} (hT : TubeTo lo hi) (hα : α ∈ Icc lo hi) :
    (∀ t ∈ Icc (0 : ℝ) (3 / 2), PhiT (fun t => (flow α t).1) (fun t => (flow α t).2.1)
      (fun t => (flow α t).2.2) t) ∧
    (0 < (flow α (3 / 2)).1 ∧ (flow α (3 / 2)).1 < 1 ∧ 0 < (flow α (3 / 2)).2.1 ∧
      (flow α (3 / 2)).2.1 < 1 ∧ 0 < (flow α (3 / 2)).2.2 ∧ (flow α (3 / 2)).2.2 < 6 / 5) :=
  hT α hα (flow α) (fun t ht => (flow_deriv α t ht.1).mono Icc_subset_Ici_self) (flow_zero α)

/-- Neither event, inside the tube: the flow solves the scaled problem with −1/2 < p < 1, p → 1
and the faster-than-every-exponential approach. -/
theorem neither_classL {lo hi α : ℝ} (hT : TubeTo lo hi) (hα : α ∈ Icc lo hi)
    (hnS : ¬ SlowL (flow α)) (hnO : ¬ Over (flow α)) :
    let F := fun t => (flow α t).1
    let P := fun t => (flow α t).2.1
    let Q := fun t => (flow α t).2.2
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt F (P η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt P (Q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(10 * F η * Q η) + 1 - P η ^ 2) (Ici 0) η) ∧
    Tendsto P atTop (𝓝 1) ∧ (∀ η ∈ Ici (0 : ℝ), -1 / 2 < P η ∧ P η < 1) ∧
    (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - P η) ≤ Q η) := by
  intro F P Q
  obtain ⟨hF, hP, hQ⟩ := comps α
  have h0 := flow_zero α
  have hP0 : P 0 = 0 := by simp [P, h0]
  obtain ⟨tube, e1, e2, e3, e4, e5, e6⟩ := tube_flow hT hα
  have hp1 : ∀ t ∈ Ici (0 : ℝ), P t ≤ 1 := by
    intro t ht
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ t from ht) with h | h
    · rw [← h, hP0]; norm_num
    · by_contra hc; push Not at hc; exact hnO ⟨t, h, hc⟩
  have U := Checked.FSNeg.LUnclamp.unclamp_from (a := 3 / 2) (by norm_num) hF hP hQ e1 e2 e3 e4 e5 e6
    (fun t ht => hp1 t (le_trans (by norm_num : (0 : ℝ) ≤ 3 / 2) ht)) (fun τ hτ => no_touch α τ (by linarith))
  -- inside the clamps everywhere
  have box : ∀ η ∈ Ici (0 : ℝ), |F η| ≤ η + 2 ∧ |P η| ≤ 2 ∧ |Q η| ≤ 2 := by
    intro η hη
    have hη0 : (0 : ℝ) ≤ η := hη
    rcases le_total η (3 / 2) with h | h
    · exact (tube η ⟨hη0, h⟩).1
    · obtain ⟨u1, u2, u3, u4, u5, u6⟩ := U η h
      exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩,
        abs_le.2 ⟨by linarith, by linarith⟩⟩
  have ceq : ∀ {c y : ℝ}, |y| ≤ c → cl c y = y := fun h => cl_of_abs_le h
  have tF : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt F (P η) (Ici 0) η := fun η hη => by
    have := hF η hη; rwa [ceq (box η hη).2.1] at this
  have tP : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt P (Q η) (Ici 0) η := fun η hη => by
    have := hP η hη; rwa [ceq (box η hη).2.2] at this
  have tQ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(10 * F η * Q η) + 1 - P η ^ 2) (Ici 0) η :=
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
        exact no_touch α η h h1 (hmax.hasDerivAt_eq_zero hd)
  have hpgt : ∀ η ∈ Ici (0 : ℝ), -1 / 2 < P η := by
    intro η hη
    rcases le_total η (3 / 2) with h | h
    · exact (tube η ⟨hη, h⟩).2
    · linarith [(U η h).1]
  have hqpos : ∀ η ∈ Ici (3 / 2 : ℝ), 0 < Q η := fun η hη => (U η hη).2.2.1
  have hlim : Tendsto P atTop (𝓝 1) :=
    Checked.FSNeg.NLimit.neg_limit (by norm_num : (0 : ℝ) < 10) tF tP tQ (by norm_num : (0 : ℝ) ≤ 3 / 2)
      hqpos (by linarith) (fun η hη => hplt η (le_trans (by norm_num : (0 : ℝ) ≤ 3 / 2) hη))
  have hft := Checked.FSNeg.NLimit.f_tendsto tF hlim
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hft.eventually_gt_atTop (11 / 30))
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 (hlim.eventually (lt_mem_nhds (show (1 : ℝ) / 3 < 1 by norm_num)))
  set a := max (max N N2) 2 with ha
  have ha0 : (0 : ℝ) ≤ a := le_trans (by norm_num) (le_max_right _ _)
  have ha2 : (2 : ℝ) ≤ a := le_max_right _ _
  have hlow : ∀ η ∈ Ici a, 3 * (1 - P η) ≤ Q η := by
    intro η hη
    have hη' : a ≤ η := hη
    by_contra hc
    push Not at hc
    apply hnS
    refine ⟨η, by linarith, fun s hs => hplt s hs.1,
      hN2 η ((le_max_right N N2).trans ((le_max_left _ _).trans hη')),
      hqpos η (show (3 / 2 : ℝ) ≤ η by linarith), hc,
      hN η ((le_max_left N N2).trans ((le_max_left _ _).trans hη'))⟩
  refine ⟨tF, tP, tQ, hlim, fun η hη => ⟨hpgt η hη, hplt η hη⟩, ?_⟩
  exact Checked.FSNeg.NRiccati.riccati_up (by norm_num : (0 : ℝ) < 10) (by norm_num : (0 : ℝ) < 3)
    tP tQ ha0 (fun η hη => hplt η (ha0.trans hη)) hft hlow

theorem core_lower {lo hi : ℝ} (hlh : lo < hi) (hO : ChainTo lo Over) (hS : ChainTo hi SlowL)
    (hT : TubeTo lo hi) :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / 10) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 / 2 < p η ∧ p η < 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      lo / Real.sqrt 10 < q 0 ∧ q 0 < hi / Real.sqrt 10 := by
  have over_lo : Over (flow lo) := of_chain hO
  have slow_hi : SlowL (flow hi) := of_chain hS
  set S : Set ℝ := {α | α ∈ Icc lo hi ∧ Over (flow α)} with hSd
  have hloS : lo ∈ S := ⟨⟨le_rfl, hlh.le⟩, over_lo⟩
  have hne : S.Nonempty := ⟨lo, hloS⟩
  have hbdd : BddAbove S := ⟨hi, fun α hα => hα.1.2⟩
  set a := sSup S with ha
  have hloa := le_csSup hbdd hloS
  obtain ⟨δ2, hδ2, hS2⟩ := slowL_open hi slow_hi
  have ha_lt : a < hi := by
    have hub : ∀ α ∈ S, α ≤ hi - δ2 / 2 := by
      intro α hα
      by_contra hc
      push Not at hc
      exact slowL_not_over (hS2 α (by rw [abs_lt]; constructor <;> linarith [hα.1.2])) hα.2
    have := csSup_le hne hub
    linarith
  have hnO : ¬ Over (flow a) := by
    intro hOa
    obtain ⟨δ, hδ, hOa'⟩ := over_open a hOa
    obtain ⟨α', hα'd⟩ : ∃ x : ℝ, x = a + min (δ / 2) ((hi - a) / 2) := ⟨_, rfl⟩
    have h1 : 0 < min (δ / 2) ((hi - a) / 2) := lt_min (by linarith) (by linarith)
    have h2 : min (δ / 2) ((hi - a) / 2) ≤ δ / 2 := min_le_left _ _
    have h3 : min (δ / 2) ((hi - a) / 2) ≤ (hi - a) / 2 := min_le_right _ _
    have hα'S : α' ∈ S := ⟨⟨by linarith, by linarith⟩,
      hOa' α' (by rw [abs_lt]; constructor <;> linarith)⟩
    have := le_csSup hbdd hα'S
    linarith
  have hnS : ¬ SlowL (flow a) := by
    intro hSa
    obtain ⟨δ, hδ, hSa'⟩ := slowL_open a hSa
    obtain ⟨α, hαS, hαa⟩ := exists_lt_of_lt_csSup hne (show a - δ < a by linarith)
    have hle : α ≤ a := le_csSup hbdd hαS
    exact slowL_not_over (hSa' α (by rw [abs_lt]; constructor <;> linarith)) hαS.2
  have hlo_lt : lo < a := by
    rcases eq_or_lt_of_le hloa with h | h
    · exact absurd (by rw [ha, ← h]; exact over_lo) hnO
    · exact h
  obtain ⟨tF, tP, tQ, hlim, hpb, hdec⟩ :=
    neither_classL hT ⟨hloa, ha_lt.le⟩ hnS hnO
  set F := fun t => (flow a t).1
  set P := fun t => (flow a t).2.1
  set Q := fun t => (flow a t).2.2
  have hF0 : F 0 = 0 := by simp [F, flow_zero]
  have hP0 : P 0 = 0 := by simp [P, flow_zero]
  have hQ0 : Q 0 = a := by simp [Q, flow_zero]
  have hc : 0 < Real.sqrt 10 := Real.sqrt_pos.2 (by norm_num)
  have hc2 : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have tQ' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(10 * F η * Q η) - (-1) * (1 - P η ^ 2)) (Ici 0) η :=
    fun η hη => (tQ η hη).congr_deriv (by ring)
  obtain ⟨A, B, C⟩ := Checked.FalknerSkan.FSScale.scale hc tF tP tQ'
  have hm := Checked.FalknerSkan.FSScale.mapsTo_div hc
  refine ⟨fun s => Real.sqrt 10 * F (s / Real.sqrt 10), fun s => P (s / Real.sqrt 10),
    fun s => Q (s / Real.sqrt 10) / Real.sqrt 10, A, B, fun s hs => ?_, by simp [hF0],
    by simp [hP0], Checked.FalknerSkan.FSScale.scale_lim hc hlim,
    fun s hs => hpb _ (hm hs), fun M => ?_, ?_, ?_⟩
  · refine (C s hs).congr_deriv ?_
    field_simp
    rw [hc2]
  · have hd := (tendsto_id.atTop_div_const hc).eventually (hdec (M * Real.sqrt 10))
    filter_upwards [hd] with s hs
    simp only [id] at hs
    rw [le_div_iff₀ hc]
    linarith
  · simp only [zero_div, hQ0]
    exact div_lt_div_of_pos_right hlo_lt hc
  · simp only [zero_div, hQ0]
    exact div_lt_div_of_pos_right ha_lt hc

end Checked.FSNeg.LAssemble
