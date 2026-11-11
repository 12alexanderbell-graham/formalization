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
import Checked.FSNeg.NFlow
import Checked.FSNeg.NUnclamp
import Checked.FSAtt.ABase
import Checked.FSAtt.AFlow
import Checked.FSAtt.AUnclamp
import Checked.FSNeg.NLimit
import Checked.FSNeg.NRiccati
import Checked.FalknerSkan.FSScale

/-! Falkner–Skan adverse pressure gradient with a free scaled coefficient at least five, the shooting argument on the scaled problem: openness and disjointness of the two event sets, a wall value in neither, and the solution it gives. Module `AAssemble`, promoted from `Work/FSAtt/AAssemble.lean`. -/

namespace Checked.FSAtt.AAssemble
open Set Filter Topology Checked.FSNeg.NBase Checked.FSSep.SBase Checked.FSAtt.ABase Checked.FSAtt.AFlow

theorem comps (K α : ℝ) :
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => (flowA K α t).1) (cl 2 (flowA K α η).2.1) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => (flowA K α t).2.1) (cl 2 (flowA K α η).2.2) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => (flowA K α t).2.2)
      (-(K * cl (max η 0 + 2) (flowA K α η).1 * cl 2 (flowA K α η).2.2) + 1 - cl 2 (flowA K α η).2.1 ^ 2)
      (Ici 0) η) := by
  refine ⟨fun η hη => ?_, fun η hη => ?_, fun η hη => ?_⟩
  · exact (hasFDerivAt_fst.comp_hasDerivWithinAt η (flowA_deriv K α η hη))
  · exact (hasFDerivAt_fst.comp_hasDerivWithinAt η
      (hasFDerivAt_snd.comp_hasDerivWithinAt η (flowA_deriv K α η hη)))
  · exact (hasFDerivAt_snd.comp_hasDerivWithinAt η
      (hasFDerivAt_snd.comp_hasDerivWithinAt η (flowA_deriv K α η hη)))

theorem slow_class {K : ℝ} (hK5 : 5 ≤ K) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 11 / 10) (hS : SlowA (flowA K α)) :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / K) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ q 0 = α / Real.sqrt K ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q η ∧ 0 ≤ p η ∧ p η ≤ 1) ∧
      (∀ᶠ η in atTop, q η < 3 * (1 - p η)) := by
  obtain ⟨hF, hP, hQ⟩ := comps K α
  set F := fun t => (flowA K α t).1
  set P := fun t => (flowA K α t).2.1
  set Q := fun t => (flowA K α t).2.2
  have h0 := flowA_zero K α
  have hF0 : F 0 = 0 := by simp [F, h0]
  have hP0 : P 0 = 0 := by simp [P, h0]
  have hQ0 : Q 0 = α := by simp [Q, h0]
  obtain ⟨η₀, hη₀, hpre, hs1, hs2, hs3⟩ := hS
  have U := Checked.FSAtt.AUnclamp.unclamp hK5 hα0 hα1 hF hP hQ hF0 hP0 hQ0 hη₀ hpre hs1 hs2 hs3

  -- the true scaled system
  have tF : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt F (P η) (Ici 0) η := fun η hη => by
    have u := U η hη
    have := hF η hη; rwa [Checked.FSAtt.AUnclamp.cl_eq (by linarith [u.1]) (by linarith [u.2.1])] at this
  have tP : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt P (Q η) (Ici 0) η := fun η hη => by
    have u := U η hη
    have := hP η hη; rwa [Checked.FSAtt.AUnclamp.cl_eq (by linarith [u.2.2.1]) (by linarith [u.2.2.2.1])] at this
  have tQ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(K * F η * Q η) + 1 - P η ^ 2) (Ici 0) η :=
    fun η hη => by
    have u := U η hη
    have hη0 : (0 : ℝ) ≤ η := hη
    have := hQ η hη
    rwa [Checked.FSAtt.AUnclamp.cl_eq (c := max η 0 + 2) (y := F η) (by rw [max_eq_left hη0]; linarith [u.2.2.2.2.1])
        (by rw [max_eq_left hη0]; linarith [u.2.2.2.2.2.1]),
      Checked.FSAtt.AUnclamp.cl_eq (c := 2) (y := Q η) (by linarith [u.2.2.1]) (by linarith [u.2.2.2.1]),
      Checked.FSAtt.AUnclamp.cl_eq (c := 2) (y := P η) (by linarith [u.1]) (by linarith [u.2.1])] at this
  have hlim : Tendsto P atTop (𝓝 1) :=
    Checked.FSNeg.NLimit.neg_limit (by linarith : (0 : ℝ) < K) tF tP tQ le_rfl
      (fun η hη => (U η hη).2.2.1) (by rw [hP0]; norm_num) (fun η hη => (U η hη).2.1)
  -- scaling back: c = √K
  have hc : 0 < Real.sqrt K := Real.sqrt_pos.2 (by linarith)
  have hc2 : Real.sqrt K ^ 2 = K := Real.sq_sqrt (by linarith)
  have hc1 : 1 < Real.sqrt K := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have tQ' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(K * F η * Q η) - (-1) * (1 - P η ^ 2)) (Ici 0) η :=
    fun η hη => (tQ η hη).congr_deriv (by ring)
  obtain ⟨A, B, C⟩ := Checked.FalknerSkan.FSScale.scale hc tF tP tQ'
  have hm := Checked.FalknerSkan.FSScale.mapsTo_div hc
  refine ⟨fun s => Real.sqrt K * F (s / Real.sqrt K), fun s => P (s / Real.sqrt K),
    fun s => Q (s / Real.sqrt K) / Real.sqrt K, A, B, fun s hs => ?_, by simp [hF0],
    by simp [hP0], by simp [hQ0], Checked.FalknerSkan.FSScale.scale_lim hc hlim, fun s hs => ?_, ?_⟩
  · refine (C s hs).congr_deriv ?_
    field_simp
    rw [hc2]
  · have u := U (s / Real.sqrt K) (hm hs)
    exact ⟨div_pos u.2.2.1 hc, u.1, u.2.1.le⟩
  · filter_upwards [eventually_ge_atTop (η₀ * Real.sqrt K)] with s hs
    have hs' : η₀ ≤ s / Real.sqrt K := by rw [le_div_iff₀ hc]; exact hs
    have hs0 : s / Real.sqrt K ∈ Ici (0 : ℝ) := hη₀.le.trans hs'
    have u := U _ hs0
    have k := (u.2.2.2.2.2.2 hs').1
    rw [div_lt_iff₀ hc]
    have : 0 < 1 - P (s / Real.sqrt K) := by linarith [u.2.1]
    nlinarith

theorem of_chain {K α : ℝ} {E : (ℝ → ℝ × ℝ × ℝ) → Prop} (h : ChainA K α E) : E (flowA K α) := by
  obtain ⟨T, _, hT⟩ := h
  exact hT (flowA K α) (fun t ht => (flowA_deriv K α t ht.1).mono Icc_subset_Ici_self) (flowA_zero K α)

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

theorem cont_comp (K α : ℝ) (η : ℝ) : ContinuousOn (flowA K α) (Icc 0 η) := fun s hs =>
  ((flowA_deriv K α s hs.1).continuousWithinAt).mono (fun x hx => hx.1)

theorem over_open (K α₀ : ℝ) (h : Over (flowA K α₀)) :
    ∃ δ > 0, ∀ α, |α - α₀| < δ → Over (flowA K α) := by
  obtain ⟨η, hη, hp⟩ := h
  obtain ⟨δ, hδ, hcl⟩ := flowA_cont K η hη.le α₀ (show 0 < (flowA K α₀ η).2.1 - 1 by linarith)
  refine ⟨δ, hδ, fun α hα => ⟨η, hη, ?_⟩⟩
  have k := (dist_c1 (a := flowA K α η) (b := flowA K α₀ η)).trans_lt (hcl α hα η ⟨hη.le, le_rfl⟩)
  rw [abs_lt] at k; linarith [k.1]

theorem slow_open (K α₀ : ℝ) (h : SlowA (flowA K α₀)) :
    ∃ δ > 0, ∀ α, |α - α₀| < δ → SlowA (flowA K α) := by
  obtain ⟨η, hη, hpre, h1, h2, h3⟩ := h
  have hcp : ContinuousOn (fun s => (flowA K α₀ s).2.1) (Icc 0 η) :=
    (continuous_fst.comp continuous_snd).comp_continuousOn (cont_comp K α₀ η)
  have hcq : ContinuousOn (fun s => (flowA K α₀ s).2.2) (Icc 0 η) :=
    (continuous_snd.comp continuous_snd).comp_continuousOn (cont_comp K α₀ η)
  obtain ⟨s1, hs1, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, ⟨le_rfl, hη.le⟩⟩ hcp
  obtain ⟨s2, hs2, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, ⟨le_rfl, hη.le⟩⟩ hcq
  have hM : (flowA K α₀ s1).2.1 < 1 := (hpre s1 hs1).1
  have hm : 0 < (flowA K α₀ s2).2.2 := (hpre s2 hs2).2
  set ε := min (min (1 - (flowA K α₀ s1).2.1) (flowA K α₀ s2).2.2)
    (min ((3 * (1 - (flowA K α₀ η).2.1) - (flowA K α₀ η).2.2) / 4) ((flowA K α₀ η).1 - 11 / 15)) with hε
  have e1 : ε ≤ 1 - (flowA K α₀ s1).2.1 := (min_le_left _ _).trans (min_le_left _ _)
  have e2 : ε ≤ (flowA K α₀ s2).2.2 := (min_le_left _ _).trans (min_le_right _ _)
  have e3 : ε ≤ (3 * (1 - (flowA K α₀ η).2.1) - (flowA K α₀ η).2.2) / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have e4 : ε ≤ (flowA K α₀ η).1 - 11 / 15 := (min_le_right _ _).trans (min_le_right _ _)
  have hε0 : 0 < ε := lt_min (lt_min (by linarith) hm) (lt_min (by linarith) (by linarith))
  obtain ⟨δ, hδ, hcl⟩ := flowA_cont K η hη.le α₀ hε0
  refine ⟨δ, hδ, fun α hα => ⟨η, hη, ?_, ?_, ?_, ?_⟩⟩
  · intro s hs
    have k := hcl α hα s hs
    have k1 := (dist_c1 (a := flowA K α s) (b := flowA K α₀ s)).trans_lt k
    have k2 := (dist_c2 (a := flowA K α s) (b := flowA K α₀ s)).trans_lt k
    have := hmax hs; have := hmin hs
    simp only [mem_setOf_eq] at *
    rw [abs_lt] at k1 k2
    constructor <;> linarith
  · -- p is nondecreasing on [0, η] because q > 0 there
    have hq : ∀ s ∈ Icc 0 η, 0 < (flowA K α s).2.2 := by
      intro s hs
      have k2 := (dist_c2 (a := flowA K α s) (b := flowA K α₀ s)).trans_lt (hcl α hα s hs)
      have := hmin hs
      simp only [mem_setOf_eq] at this
      rw [abs_lt] at k2; linarith
    obtain ⟨_, hP, _⟩ := comps K α
    have hm := Checked.FalknerSkan.LimitCore.mono hP le_rfl (b := η) (fun x hx => by
      have h := hq x ⟨hx.1.le, hx.2.le⟩
      unfold cl; exact le_max_of_le_right (le_min (by norm_num) h.le))
    have := hm ⟨le_rfl, hη.le⟩ ⟨hη.le, le_rfl⟩ hη.le
    simp only [flowA_zero] at this
    exact this
  · have k := hcl α hα η ⟨hη.le, le_rfl⟩
    have k1 := (dist_c1 (a := flowA K α η) (b := flowA K α₀ η)).trans_lt k
    have k2 := (dist_c2 (a := flowA K α η) (b := flowA K α₀ η)).trans_lt k
    rw [abs_lt] at k1 k2; linarith
  · have k0 := (dist_c0 (a := flowA K α η) (b := flowA K α₀ η)).trans_lt (hcl α hα η ⟨hη.le, le_rfl⟩)
    rw [abs_lt] at k0; linarith

theorem slow_not_over {K : ℝ} (hK5 : 5 ≤ K) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 11 / 10) (hS : SlowA (flowA K α))
    (hO : Over (flowA K α)) : False := by
  obtain ⟨hF, hP, hQ⟩ := comps K α
  obtain ⟨η₀, hη₀, hpre, hs1, hs2, hs3⟩ := hS
  have U := Checked.FSAtt.AUnclamp.unclamp hK5 hα0 hα1 hF hP hQ (by simp [flowA_zero]) (by simp [flowA_zero])
    (by simp [flowA_zero]) hη₀ hpre hs1 hs2 hs3
  obtain ⟨η, hη, hp⟩ := hO
  have := (U η hη.le).2.1
  linarith

/-- Neither event: the flow is a solution of the scaled problem in the decay class. -/
theorem neither_class {K : ℝ} (hK5 : 5 ≤ K) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 11 / 10) (hnS : ¬ SlowA (flowA K α))
    (hnO : ¬ Over (flowA K α)) :
    let F := fun t => (flowA K α t).1
    let P := fun t => (flowA K α t).2.1
    let Q := fun t => (flowA K α t).2.2
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt F (P η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt P (Q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(K * F η * Q η) + 1 - P η ^ 2) (Ici 0) η) ∧
    Tendsto P atTop (𝓝 1) ∧ (∀ η ∈ Ici (0 : ℝ), 0 < Q η) ∧
    (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - P η) ≤ Q η) := by
  intro F P Q
  obtain ⟨hF, hP, hQ⟩ := comps K α
  have h0 := flowA_zero K α
  have hF0 : F 0 = 0 := by simp [F, h0]
  have hP0 : P 0 = 0 := by simp [P, h0]
  have hQ0 : Q 0 = α := by simp [Q, h0]
  have hp1 : ∀ t ∈ Ici (0 : ℝ), P t ≤ 1 := by
    intro t ht
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ t from ht) with h | h
    · rw [← h, hP0]; norm_num
    · by_contra hc; push Not at hc; exact hnO ⟨t, h, hc⟩
  have htouch : ∀ τ, 0 < τ → P τ = 1 → Q τ = 0 → False := by
    intro τ hτ hpτ hqτ
    set Z : ℝ → ℝ × ℝ × ℝ := fun t => (F τ + (t - τ), 1, 0) with hZ
    have hZd : ∀ t ∈ Icc 0 τ, HasDerivWithinAt Z (vS K t (Z t)) (Icc 0 τ) t := by
      intro t _
      have hv : vS K t (Z t) = (1, 0, 0) := by
        simp only [hZ, vS]
        rw [Checked.FSAtt.AUnclamp.cl_eq (c := 2) (y := 1) (by norm_num) (by norm_num),
          Checked.FSAtt.AUnclamp.cl_eq (c := 2) (y := 0) (by norm_num) (by norm_num)]
        simp
      rw [hv]
      have a1 : HasDerivWithinAt (fun t => F τ + (t - τ)) 1 (Icc 0 τ) t :=
        ((hasDerivWithinAt_id t _).sub_const τ).const_add _ |>.congr_deriv (by simp)
      exact a1.prodMk ((hasDerivWithinAt_const t _ (1 : ℝ)).prodMk (hasDerivWithinAt_const t _ (0 : ℝ)))
    have hY : ∀ t ∈ Icc 0 τ, HasDerivWithinAt (flowA K α) (vS K t (flowA K α t)) (Icc 0 τ) t :=
      fun t ht => (flowA_deriv K α t ht.1).mono (fun x hx => hx.1)
    have hZτ : flowA K α τ = Z τ := by
      simp only [hZ, sub_self, add_zero]
      ext
      · rfl
      · exact hpτ
      · exact hqτ
    have := Checked.FSSep.SFlow.unique_left hτ.le hY hZd hZτ (⟨le_rfl, hτ.le⟩ : (0 : ℝ) ∈ Icc 0 τ)
    have h2 := congrArg (fun y => y.2.1) this
    simp only [hZ, h0] at h2
    norm_num at h2
  have U := Checked.FSAtt.AUnclamp.unclamp_neither hK5 hα0 hα1 hF hP hQ hF0 hP0 hQ0 hp1 htouch
  have ceq := @Checked.FSAtt.AUnclamp.cl_eq
  have tF : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt F (P η) (Ici 0) η := fun η hη => by
    have u := U η hη
    have := hF η hη; rwa [ceq (by linarith [u.1]) (by linarith [u.2.1])] at this
  have tP : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt P (Q η) (Ici 0) η := fun η hη => by
    have u := U η hη
    have := hP η hη; rwa [ceq (by linarith [u.2.2.1]) (by linarith [u.2.2.2.1])] at this
  have tQ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(K * F η * Q η) + 1 - P η ^ 2) (Ici 0) η :=
    fun η hη => by
    have u := U η hη
    have hη0 : (0 : ℝ) ≤ η := hη
    have := hQ η hη
    rwa [ceq (c := max η 0 + 2) (y := F η) (by rw [max_eq_left hη0]; linarith [u.2.2.2.2.1])
        (by rw [max_eq_left hη0]; linarith [u.2.2.2.2.2]),
      ceq (c := 2) (y := Q η) (by linarith [u.2.2.1]) (by linarith [u.2.2.2.1]),
      ceq (c := 2) (y := P η) (by linarith [u.1]) (by linarith [u.2.1])] at this
  have hqpos : ∀ η ∈ Ici (0 : ℝ), 0 < Q η := fun η hη => (U η hη).2.2.1
  have hplt : ∀ η ∈ Ici (0 : ℝ), P η < 1 := by
    intro η hη
    have hη0 : (0 : ℝ) ≤ η := hη
    have hsm := Checked.FalknerSkan.LimitCore.smono tP hη0 (b := η + 1)
      (fun x hx => hqpos x (hη0.trans hx.1.le))
    have := hsm ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
    linarith [hp1 (η + 1) (show (0 : ℝ) ≤ η + 1 by linarith)]
  have hlim : Tendsto P atTop (𝓝 1) :=
    Checked.FSNeg.NLimit.neg_limit (by linarith : (0 : ℝ) < K) tF tP tQ le_rfl
      hqpos (by rw [hP0]; norm_num) hplt
  have hft := Checked.FSNeg.NLimit.f_tendsto tF hlim
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hft.eventually_gt_atTop (11 / 15))
  set a := max N 1 with ha
  have ha0 : (0 : ℝ) ≤ a := le_trans (by norm_num) (le_max_right _ _)
  have hlow : ∀ η ∈ Ici a, 3 * (1 - P η) ≤ Q η := by
    intro η hη
    have hη' : a ≤ η := hη
    by_contra hc
    push Not at hc
    apply hnS
    refine ⟨η, lt_of_lt_of_le (by norm_num) ((le_max_right N 1).trans hη'), fun s hs => ?_,
      (U η (ha0.trans hη')).1, hc, hN η ((le_max_left N 1).trans hη')⟩
    exact ⟨hplt s hs.1, hqpos s hs.1⟩
  refine ⟨tF, tP, tQ, hlim, hqpos, ?_⟩
  exact Checked.FSNeg.NRiccati.riccati_up (by linarith : (0 : ℝ) < K) (by norm_num : (0 : ℝ) < 3)
    tP tQ ha0 (fun η hη => hplt η (ha0.trans hη)) hft hlow

end Checked.FSAtt.AAssemble
