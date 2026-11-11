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
import Checked.FSSep.SUnclamp
import Checked.FSNeg.NLimit
import Checked.FSNeg.NRiccati
import Checked.FalknerSkan.FSScale

/-! Falkner–Skan separation, the shooting argument in the coefficient: openness and disjointness of the two event sets, a coefficient in neither, and the separation profile it gives. Module `SAssemble`, promoted from `Work/FSSep/SAssemble.lean`. -/

namespace Checked.FSSep.SAssemble
open Set Filter Topology Checked.FSNeg.NBase Checked.FSSep.SBase Checked.FSSep.SFlow

theorem comps (K : ℝ) :
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => (flowK K t).1) (cl 2 (flowK K η).2.1) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => (flowK K t).2.1) (cl 2 (flowK K η).2.2) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => (flowK K t).2.2)
      (-(K * cl (max η 0 + 2) (flowK K η).1 * cl 2 (flowK K η).2.2) + 1 - cl 2 (flowK K η).2.1 ^ 2)
      (Ici 0) η) := by
  refine ⟨fun η hη => ?_, fun η hη => ?_, fun η hη => ?_⟩
  · exact (hasFDerivAt_fst.comp_hasDerivWithinAt η (flowK_deriv K η hη))
  · exact (hasFDerivAt_fst.comp_hasDerivWithinAt η
      (hasFDerivAt_snd.comp_hasDerivWithinAt η (flowK_deriv K η hη)))
  · exact (hasFDerivAt_snd.comp_hasDerivWithinAt η
      (hasFDerivAt_snd.comp_hasDerivWithinAt η (flowK_deriv K η hη)))

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

theorem cont_comp (K : ℝ) (η : ℝ) : ContinuousOn (flowK K) (Icc 0 η) := fun s hs =>
  ((flowK_deriv K s hs.1).continuousWithinAt).mono (fun x hx => hx.1)

theorem over_open (K₀ : ℝ) (h : Over (flowK K₀)) :
    ∃ δ > 0, ∀ K, |K - K₀| < δ → Over (flowK K) := by
  obtain ⟨η, hη, hp⟩ := h
  obtain ⟨δ, hδ, hcl⟩ := flowK_cont η hη.le K₀ (show 0 < (flowK K₀ η).2.1 - 1 by linarith)
  refine ⟨δ, hδ, fun K hK => ⟨η, hη, ?_⟩⟩
  have k := (dist_c1 (a := flowK K η) (b := flowK K₀ η)).trans_lt (hcl K hK η ⟨hη.le, le_rfl⟩)
  rw [abs_lt] at k; linarith [k.1]

/-- Along a SlowS trajectory with K ≥ 5, every clamp is inactive (`SUnclamp.unclampS`). -/
theorem slow_unclamp {K : ℝ} (hK5 : 5 ≤ K) {η₀ : ℝ} (hη₀ : 0 < η₀)
    (hpre : ∀ s ∈ Icc 0 η₀, (flowK K s).2.1 < 1) (hs1 : 0 ≤ (flowK K η₀).2.1)
    (hs2 : (flowK K η₀).2.2 < 3 * (1 - (flowK K η₀).2.1)) (hs3 : 11 / 15 < (flowK K η₀).1) :
    ∀ t ∈ Ici (0 : ℝ), 0 ≤ (flowK K t).2.1 ∧ (flowK K t).2.1 < 1 ∧ 0 ≤ (flowK K t).2.2 ∧
      (0 < t → 0 < (flowK K t).2.2) ∧ (flowK K t).2.2 < 2 ∧ 0 ≤ (flowK K t).1 ∧ (flowK K t).1 ≤ t ∧
      (η₀ ≤ t → (flowK K t).2.2 < 3 * (1 - (flowK K t).2.1) ∧ 11 / 15 < (flowK K t).1) := by
  obtain ⟨hF, hP, hQ⟩ := comps K
  exact Checked.FSSep.SUnclamp.unclampS hK5 hF hP hQ (by simp [flowK_zero]) (by simp [flowK_zero])
    (by simp [flowK_zero]) hη₀ hpre hs1 hs2 hs3

theorem slowS_open (K₀ : ℝ) (hK₀ : 5 ≤ K₀) (h : SlowS (flowK K₀)) :
    ∃ δ > 0, ∀ K, |K - K₀| < δ → SlowS (flowK K) := by
  obtain ⟨η, hη, hpre, h1, h2, h3⟩ := h
  have U := slow_unclamp hK₀ hη hpre h1 h2 h3
  -- p(η) > 0 strictly: p is strictly increasing on [0, η] since q > 0 on (0, η)
  have hpη : 0 < (flowK K₀ η).2.1 := by
    obtain ⟨_, hP, _⟩ := comps K₀
    have hsm := Checked.FalknerSkan.LimitCore.smono hP le_rfl (b := η) (fun x hx => by
      have u := U x hx.1.le
      rw [Checked.FSSep.SUnclamp.cl_eq (by linarith [u.2.2.1]) (by linarith [u.2.2.2.2.1])]
      exact u.2.2.2.1 hx.1)
    have := hsm ⟨le_rfl, hη.le⟩ ⟨hη.le, le_rfl⟩ hη
    simpa [flowK_zero] using this
  have hcp : ContinuousOn (fun s => (flowK K₀ s).2.1) (Icc 0 η) :=
    (continuous_fst.comp continuous_snd).comp_continuousOn (cont_comp K₀ η)
  obtain ⟨s1, hs1, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, ⟨le_rfl, hη.le⟩⟩ hcp
  have hM : (flowK K₀ s1).2.1 < 1 := hpre s1 hs1
  set ε := min (min (1 - (flowK K₀ s1).2.1) (flowK K₀ η).2.1)
    (min ((3 * (1 - (flowK K₀ η).2.1) - (flowK K₀ η).2.2) / 4) ((flowK K₀ η).1 - 11 / 15)) with hε
  have e1 : ε ≤ 1 - (flowK K₀ s1).2.1 := (min_le_left _ _).trans (min_le_left _ _)
  have e2 : ε ≤ (flowK K₀ η).2.1 := (min_le_left _ _).trans (min_le_right _ _)
  have e3 : ε ≤ (3 * (1 - (flowK K₀ η).2.1) - (flowK K₀ η).2.2) / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have e4 : ε ≤ (flowK K₀ η).1 - 11 / 15 := (min_le_right _ _).trans (min_le_right _ _)
  have hε0 : 0 < ε := lt_min (lt_min (by linarith) hpη) (lt_min (by linarith) (by linarith))
  obtain ⟨δ, hδ, hcl⟩ := flowK_cont η hη.le K₀ hε0
  refine ⟨δ, hδ, fun K hK => ⟨η, hη, ?_, ?_, ?_, ?_⟩⟩
  · intro s hs
    have k1 := (dist_c1 (a := flowK K s) (b := flowK K₀ s)).trans_lt (hcl K hK s hs)
    have := hmax hs
    simp only [mem_setOf_eq] at this
    rw [abs_lt] at k1
    linarith
  · have k1 := (dist_c1 (a := flowK K η) (b := flowK K₀ η)).trans_lt (hcl K hK η ⟨hη.le, le_rfl⟩)
    rw [abs_lt] at k1; linarith
  · have k := hcl K hK η ⟨hη.le, le_rfl⟩
    have k1 := (dist_c1 (a := flowK K η) (b := flowK K₀ η)).trans_lt k
    have k2 := (dist_c2 (a := flowK K η) (b := flowK K₀ η)).trans_lt k
    rw [abs_lt] at k1 k2; linarith
  · have k0 := (dist_c0 (a := flowK K η) (b := flowK K₀ η)).trans_lt (hcl K hK η ⟨hη.le, le_rfl⟩)
    rw [abs_lt] at k0; linarith

theorem slowS_not_over {K : ℝ} (hK5 : 5 ≤ K) (hS : SlowS (flowK K)) (hO : Over (flowK K)) :
    False := by
  obtain ⟨η₀, hη₀, hpre, hs1, hs2, hs3⟩ := hS
  have U := slow_unclamp hK5 hη₀ hpre hs1 hs2 hs3
  obtain ⟨η, hη, hp⟩ := hO
  have := (U η hη.le).2.1
  linarith

/-- Neither event: the flow solves the scaled problem with zero wall shear, in the decay class. -/
theorem neither_class {K : ℝ} (hK : 0 < K) (hnS : ¬ SlowS (flowK K)) (hnO : ¬ Over (flowK K)) :
    let F := fun t => (flowK K t).1
    let P := fun t => (flowK K t).2.1
    let Q := fun t => (flowK K t).2.2
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt F (P η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt P (Q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(K * F η * Q η) + 1 - P η ^ 2) (Ici 0) η) ∧
    Tendsto P atTop (𝓝 1) ∧ (∀ η ∈ Ioi (0 : ℝ), 0 < Q η) ∧
    (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - P η) ≤ Q η) := by
  intro F P Q
  obtain ⟨hF, hP, hQ⟩ := comps K
  have h0 := flowK_zero K
  have hF0 : F 0 = 0 := by simp [F, h0]
  have hP0 : P 0 = 0 := by simp [P, h0]
  have hQ0 : Q 0 = 0 := by simp [Q, h0]
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
        rw [Checked.FSSep.SUnclamp.cl_eq (c := 2) (y := 1) (by norm_num) (by norm_num),
          Checked.FSSep.SUnclamp.cl_eq (c := 2) (y := 0) (by norm_num) (by norm_num)]
        simp
      rw [hv]
      have a1 : HasDerivWithinAt (fun t => F τ + (t - τ)) 1 (Icc 0 τ) t :=
        ((hasDerivWithinAt_id t _).sub_const τ).const_add _ |>.congr_deriv (by simp)
      exact a1.prodMk ((hasDerivWithinAt_const t _ (1 : ℝ)).prodMk (hasDerivWithinAt_const t _ (0 : ℝ)))
    have hY : ∀ t ∈ Icc 0 τ, HasDerivWithinAt (flowK K) (vS K t (flowK K t)) (Icc 0 τ) t :=
      fun t ht => (flowK_deriv K t ht.1).mono (fun x hx => hx.1)
    have hZτ : flowK K τ = Z τ := by
      simp only [hZ, sub_self, add_zero]
      ext
      · rfl
      · exact hpτ
      · exact hqτ
    have := unique_left hτ.le hY hZd hZτ (⟨le_rfl, hτ.le⟩ : (0 : ℝ) ∈ Icc 0 τ)
    have h2 := congrArg (fun y => y.2.1) this
    simp only [hZ, h0] at h2
    norm_num at h2
  have U := Checked.FSSep.SUnclamp.unclampS_neither hK hF hP hQ hF0 hP0 hQ0 hp1 htouch
  have ceq := @Checked.FSSep.SUnclamp.cl_eq
  have tF : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt F (P η) (Ici 0) η := fun η hη => by
    have u := U η hη
    have := hF η hη; rwa [ceq (by linarith [u.1]) (by linarith [u.2.1])] at this
  have tP : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt P (Q η) (Ici 0) η := fun η hη => by
    have u := U η hη
    have := hP η hη; rwa [ceq (by linarith [u.2.2.1]) (by linarith [u.2.2.2.2.1])] at this
  have tQ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(K * F η * Q η) + 1 - P η ^ 2) (Ici 0) η :=
    fun η hη => by
    have u := U η hη
    have hη0 : (0 : ℝ) ≤ η := hη
    have := hQ η hη
    rwa [ceq (c := max η 0 + 2) (y := F η) (by rw [max_eq_left hη0]; linarith [u.2.2.2.2.2.1])
        (by rw [max_eq_left hη0]; linarith [u.2.2.2.2.2.2]),
      ceq (c := 2) (y := Q η) (by linarith [u.2.2.1]) (by linarith [u.2.2.2.2.1]),
      ceq (c := 2) (y := P η) (by linarith [u.1]) (by linarith [u.2.1])] at this
  have hqpos : ∀ η ∈ Ioi (0 : ℝ), 0 < Q η := fun η hη => (U η (le_of_lt (show (0 : ℝ) < η from hη))).2.2.2.1 hη
  have hplt : ∀ η ∈ Ici (0 : ℝ), P η < 1 := by
    intro η hη
    have hη0 : (0 : ℝ) ≤ η := hη
    have hsm := Checked.FalknerSkan.LimitCore.smono tP hη0 (b := η + 1)
      (fun x hx => hqpos x (lt_of_le_of_lt hη0 hx.1))
    have := hsm ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
    linarith [hp1 (η + 1) (show (0 : ℝ) ≤ η + 1 by linarith)]
  have hlim : Tendsto P atTop (𝓝 1) :=
    Checked.FSNeg.NLimit.neg_limit hK tF tP tQ (a := 1) (by norm_num)
      (fun η hη => hqpos η (show (0 : ℝ) < η from lt_of_lt_of_le one_pos hη))
      (by linarith [(U 1 (by norm_num)).1]) (fun η hη => hplt η (show (0 : ℝ) ≤ η from le_trans zero_le_one hη))
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
    exact hplt s hs.1
  refine ⟨tF, tP, tQ, hlim, hqpos, ?_⟩
  exact Checked.FSNeg.NRiccati.riccati_up hK (by norm_num : (0 : ℝ) < 3)
    tP tQ ha0 (fun η hη => hplt η (ha0.trans hη)) hft hlow

theorem core_sep (hO : ChainK (10000000000 / 1988377351) Over)
    (hS : ChainK (10000000000 / 1988377350) SlowS) :
    ∃ β ∈ Ioo (-(1988377351 / 10000000000 : ℝ)) (-(1988377350 / 10000000000)),
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ q 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ioi (0 : ℝ), 0 < q η) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) := by
  set lo : ℝ := 10000000000 / 1988377351 with hlo
  set hi : ℝ := 10000000000 / 1988377350 with hhi
  have hlh : lo < hi := by rw [hlo, hhi]; norm_num
  have hlo5 : (5 : ℝ) ≤ lo := by rw [hlo]; norm_num
  have over_lo : Over (flowK lo) := of_chain hO
  have slow_hi : SlowS (flowK hi) := of_chain hS
  have hβlo : 1 / lo = 1988377351 / 10000000000 := by rw [hlo]; norm_num
  have hβhi : 1 / hi = 1988377350 / 10000000000 := by rw [hhi]; norm_num
  clear_value lo hi
  set S : Set ℝ := {K | K ∈ Icc lo hi ∧ Over (flowK K)} with hSd
  have hloS : lo ∈ S := ⟨⟨le_rfl, hlh.le⟩, over_lo⟩
  have hne : S.Nonempty := ⟨lo, hloS⟩
  have hbdd : BddAbove S := ⟨hi, fun K hK => hK.1.2⟩
  set a := sSup S with ha
  have hloa := le_csSup hbdd hloS
  obtain ⟨δ2, hδ2, hS2⟩ := slowS_open hi (by linarith) slow_hi
  have ha_lt : a < hi := by
    have hub : ∀ K ∈ S, K ≤ hi - δ2 / 2 := by
      intro K hK
      by_contra hc
      push Not at hc
      have hSK := hS2 K (by rw [abs_lt]; constructor <;> linarith [hK.1.2])
      exact slowS_not_over (by linarith [hK.1.1]) hSK hK.2
    have := csSup_le hne hub
    linarith
  have hnO : ¬ Over (flowK a) := by
    intro hOa
    obtain ⟨δ, hδ, hOa'⟩ := over_open a hOa
    obtain ⟨K', hK'd⟩ : ∃ x : ℝ, x = a + min (δ / 2) ((hi - a) / 2) := ⟨_, rfl⟩
    have h1 : 0 < min (δ / 2) ((hi - a) / 2) := lt_min (by linarith) (by linarith)
    have h2 : min (δ / 2) ((hi - a) / 2) ≤ δ / 2 := min_le_left _ _
    have h3 : min (δ / 2) ((hi - a) / 2) ≤ (hi - a) / 2 := min_le_right _ _
    have hK'S : K' ∈ S := ⟨⟨by linarith, by linarith⟩,
      hOa' K' (by rw [abs_lt]; constructor <;> linarith)⟩
    have := le_csSup hbdd hK'S
    linarith
  have hnS : ¬ SlowS (flowK a) := by
    intro hSa
    obtain ⟨δ, hδ, hSa'⟩ := slowS_open a (by linarith) hSa
    obtain ⟨K, hKS, hKa⟩ := exists_lt_of_lt_csSup hne (show a - δ < a by linarith)
    have hle : K ≤ a := le_csSup hbdd hKS
    exact slowS_not_over (by linarith [hKS.1.1])
      (hSa' K (by rw [abs_lt]; constructor <;> linarith)) hKS.2
  have hlo_lt : lo < a := by
    rcases eq_or_lt_of_le hloa with h | h
    · exact absurd (by rw [ha, ← h]; exact over_lo) hnO
    · exact h
  have ha0 : 0 < a := by linarith
  obtain ⟨tF, tP, tQ, hlim, hqpos, hdec⟩ := neither_class ha0 hnS hnO
  set F := fun t => (flowK a t).1
  set P := fun t => (flowK a t).2.1
  set Q := fun t => (flowK a t).2.2
  have hF0 : F 0 = 0 := by simp [F, flowK_zero]
  have hP0 : P 0 = 0 := by simp [P, flowK_zero]
  have hQ0 : Q 0 = 0 := by simp [Q, flowK_zero]
  have hc : 0 < Real.sqrt a := Real.sqrt_pos.2 ha0
  have hc2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha0.le
  have tQ' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(a * F η * Q η) - (-1) * (1 - P η ^ 2)) (Ici 0) η :=
    fun η hη => (tQ η hη).congr_deriv (by ring)
  obtain ⟨A, B, C⟩ := Checked.FalknerSkan.FSScale.scale hc tF tP tQ'
  have hm := Checked.FalknerSkan.FSScale.mapsTo_div hc
  have hinv1 : 1 / a < 1 / lo := one_div_lt_one_div_of_lt (by linarith) hlo_lt
  have hinv2 : 1 / hi < 1 / a := one_div_lt_one_div_of_lt ha0 ha_lt
  refine ⟨-(1 / a), ⟨by rw [hβlo] at hinv1; linarith, by rw [hβhi] at hinv2; linarith⟩,
    fun s => Real.sqrt a * F (s / Real.sqrt a), fun s => P (s / Real.sqrt a),
    fun s => Q (s / Real.sqrt a) / Real.sqrt a, A, B, fun s hs => ?_, by simp [hF0],
    by simp [hP0], by simp [hQ0], Checked.FalknerSkan.FSScale.scale_lim hc hlim,
    fun s hs => div_pos (hqpos _ (div_pos hs hc)) hc, fun M => ?_⟩
  · refine (C s hs).congr_deriv ?_
    rw [hc2]
    field_simp
  · have hd := (tendsto_id.atTop_div_const hc).eventually (hdec (M * Real.sqrt a))
    filter_upwards [hd] with s hs
    simp only [id] at hs
    rw [le_div_iff₀ hc]
    linarith

end Checked.FSSep.SAssemble
