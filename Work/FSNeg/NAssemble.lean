import Mathlib
import Work.FSNeg.NFlow
import Work.FSNeg.NUnclamp
import Work.FSNeg.NLimit
import Work.FSNeg.NRiccati
import Checked.FalknerSkan.FSScale

/-!
# Falkner–Skan β = −1/10: a Slow trajectory is a boundary-value solution (run 2026-11-09T0828Z)

`slow_class`: if the clamped flow `NFlow.flow α` (0 < α ≤ 11/10) has the Slow event, its clamps never
act (`NUnclamp.unclamp`), it solves F''' + 10 F F'' + 1 − F'² = 0 on [0, ∞) with 0 ≤ F' < 1,
F'' > 0, F' → 1 (Lemma L, `NLimit.neg_limit`) and eventually F'' < 3(1 − F'); the scaling
f(η) = F(√10 η)/√10 (`Checked.FalknerSkan.FSScale.scale` with a = 10, b = −1, c = √10) gives a
solution of f''' + f f'' − (1 − f'²)/10 = 0 with f''(0) = α/√10.
`core_not_unique`: Slow at α = 1/2 and α = 3/4 (the certified chains, as hypotheses) give
`NegTenth.fs_neg_tenth_not_unique`.
-/

namespace Work.FSNeg.NAssemble
open Set Filter Topology Work.FSNeg.NBase Work.FSNeg.NFlow

theorem comps (α : ℝ) :
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => (flow α t).1) (cl 2 (flow α η).2.1) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => (flow α t).2.1) (cl 2 (flow α η).2.2) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => (flow α t).2.2)
      (-(10 * cl (max η 0 + 2) (flow α η).1 * cl 2 (flow α η).2.2) + 1 - cl 2 (flow α η).2.1 ^ 2)
      (Ici 0) η) := by
  refine ⟨fun η hη => ?_, fun η hη => ?_, fun η hη => ?_⟩
  · exact (hasFDerivAt_fst.comp_hasDerivWithinAt η (flow_deriv α η hη))
  · exact (hasFDerivAt_fst.comp_hasDerivWithinAt η
      (hasFDerivAt_snd.comp_hasDerivWithinAt η (flow_deriv α η hη)))
  · exact (hasFDerivAt_snd.comp_hasDerivWithinAt η
      (hasFDerivAt_snd.comp_hasDerivWithinAt η (flow_deriv α η hη)))

theorem slow_class {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 11 / 10) (hS : Slow (flow α)) :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / 10) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ q 0 = α / Real.sqrt 10 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q η ∧ 0 ≤ p η ∧ p η ≤ 1) ∧
      (∀ᶠ η in atTop, q η < 3 * (1 - p η)) := by
  obtain ⟨hF, hP, hQ⟩ := comps α
  set F := fun t => (flow α t).1
  set P := fun t => (flow α t).2.1
  set Q := fun t => (flow α t).2.2
  have h0 := flow_zero α
  have hF0 : F 0 = 0 := by simp [F, h0]
  have hP0 : P 0 = 0 := by simp [P, h0]
  have hQ0 : Q 0 = α := by simp [Q, h0]
  obtain ⟨η₀, hη₀, hpre, hs1, hs2, hs3⟩ := hS
  have U := Work.FSNeg.NUnclamp.unclamp hα0 hα1 hF hP hQ hF0 hP0 hQ0 hη₀ hpre hs1 hs2 hs3

  -- the true scaled system
  have tF : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt F (P η) (Ici 0) η := fun η hη => by
    have u := U η hη
    have := hF η hη; rwa [Work.FSNeg.NUnclamp.cl_eq (by linarith [u.1]) (by linarith [u.2.1])] at this
  have tP : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt P (Q η) (Ici 0) η := fun η hη => by
    have u := U η hη
    have := hP η hη; rwa [Work.FSNeg.NUnclamp.cl_eq (by linarith [u.2.2.1]) (by linarith [u.2.2.2.1])] at this
  have tQ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(10 * F η * Q η) + 1 - P η ^ 2) (Ici 0) η :=
    fun η hη => by
    have u := U η hη
    have hη0 : (0 : ℝ) ≤ η := hη
    have := hQ η hη
    rwa [Work.FSNeg.NUnclamp.cl_eq (c := max η 0 + 2) (y := F η) (by rw [max_eq_left hη0]; linarith [u.2.2.2.2.1])
        (by rw [max_eq_left hη0]; linarith [u.2.2.2.2.2.1]),
      Work.FSNeg.NUnclamp.cl_eq (c := 2) (y := Q η) (by linarith [u.2.2.1]) (by linarith [u.2.2.2.1]),
      Work.FSNeg.NUnclamp.cl_eq (c := 2) (y := P η) (by linarith [u.1]) (by linarith [u.2.1])] at this
  have hlim : Tendsto P atTop (𝓝 1) :=
    Work.FSNeg.NLimit.neg_limit (by norm_num : (0 : ℝ) < 10) tF tP tQ le_rfl
      (fun η hη => (U η hη).2.2.1) (by rw [hP0]; norm_num) (fun η hη => (U η hη).2.1)
  -- scaling back: c = √10
  have hc : 0 < Real.sqrt 10 := Real.sqrt_pos.2 (by norm_num)
  have hc2 : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have hc1 : 1 < Real.sqrt 10 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have tQ' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(10 * F η * Q η) - (-1) * (1 - P η ^ 2)) (Ici 0) η :=
    fun η hη => (tQ η hη).congr_deriv (by ring)
  obtain ⟨A, B, C⟩ := Checked.FalknerSkan.FSScale.scale hc tF tP tQ'
  have hm := Checked.FalknerSkan.FSScale.mapsTo_div hc
  refine ⟨fun s => Real.sqrt 10 * F (s / Real.sqrt 10), fun s => P (s / Real.sqrt 10),
    fun s => Q (s / Real.sqrt 10) / Real.sqrt 10, A, B, fun s hs => ?_, by simp [hF0],
    by simp [hP0], by simp [hQ0], Checked.FalknerSkan.FSScale.scale_lim hc hlim, fun s hs => ?_, ?_⟩
  · refine (C s hs).congr_deriv ?_
    field_simp
    rw [hc2]
  · have u := U (s / Real.sqrt 10) (hm hs)
    exact ⟨div_pos u.2.2.1 hc, u.1, u.2.1.le⟩
  · filter_upwards [eventually_ge_atTop (η₀ * Real.sqrt 10)] with s hs
    have hs' : η₀ ≤ s / Real.sqrt 10 := by rw [le_div_iff₀ hc]; exact hs
    have hs0 : s / Real.sqrt 10 ∈ Ici (0 : ℝ) := hη₀.le.trans hs'
    have u := U _ hs0
    have k := (u.2.2.2.2.2.2 hs').1
    rw [div_lt_iff₀ hc]
    have : 0 < 1 - P (s / Real.sqrt 10) := by linarith [u.2.1]
    nlinarith

/-- The certified chain shape: every solution of the clamped field on [0, T] from (0, 0, α) has
the event `E`. -/
def ChainTo (α : ℝ) (E : (ℝ → ℝ × ℝ × ℝ) → Prop) : Prop :=
  ∃ T > 0, ∀ Y : ℝ → ℝ × ℝ × ℝ, (∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vN t (Y t)) (Icc 0 T) t) →
    Y 0 = (0, 0, α) → E Y

theorem of_chain {α : ℝ} {E : (ℝ → ℝ × ℝ × ℝ) → Prop} (h : ChainTo α E) : E (flow α) := by
  obtain ⟨T, _, hT⟩ := h
  exact hT (flow α) (fun t ht => (flow_deriv α t ht.1).mono Icc_subset_Ici_self) (flow_zero α)

theorem core_not_unique (hS1 : ChainTo (1 / 2) Slow) (hS2 : ChainTo (3 / 4) Slow) :
    ∃ f p q f₂ p₂ q₂ : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / 10) * (1 - p η ^ 2)) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - (-1 / 10) * (1 - p₂ η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ f₂ 0 = 0 ∧ p₂ 0 = 0 ∧
      Tendsto p atTop (𝓝 1) ∧ Tendsto p₂ atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q η ∧ 0 ≤ p η ∧ p η ≤ 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q₂ η ∧ 0 ≤ p₂ η ∧ p₂ η ≤ 1) ∧
      (∀ᶠ η in atTop, q η < 3 * (1 - p η)) ∧ (∀ᶠ η in atTop, q₂ η < 3 * (1 - p₂ η)) ∧
      q 0 ≠ q₂ 0 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ :=
    slow_class (by norm_num) (by norm_num) (of_chain hS1)
  obtain ⟨f₂, p₂, q₂, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ :=
    slow_class (by norm_num) (by norm_num) (of_chain hS2)
  refine ⟨f, p, q, f₂, p₂, q₂, a1, a2, a3, b1, b2, b3, a4, a5, b4, b5, a7, b7, a8, b8, a9, b9, ?_⟩
  rw [a6, b6]
  have hc : 0 < Real.sqrt 10 := Real.sqrt_pos.2 (by norm_num)
  intro h
  rw [div_left_inj' hc.ne'] at h
  norm_num at h

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

theorem cont_comp (α : ℝ) (η : ℝ) : ContinuousOn (flow α) (Icc 0 η) := fun s hs =>
  ((flow_deriv α s hs.1).continuousWithinAt).mono (fun x hx => hx.1)

theorem over_open (α₀ : ℝ) (h : Over (flow α₀)) :
    ∃ δ > 0, ∀ α, |α - α₀| < δ → Over (flow α) := by
  obtain ⟨η, hη, hp⟩ := h
  obtain ⟨δ, hδ, hcl⟩ := flow_cont η hη.le α₀ (show 0 < (flow α₀ η).2.1 - 1 by linarith)
  refine ⟨δ, hδ, fun α hα => ⟨η, hη, ?_⟩⟩
  have k := (dist_c1 (a := flow α η) (b := flow α₀ η)).trans_lt (hcl α hα η ⟨hη.le, le_rfl⟩)
  rw [abs_lt] at k; linarith [k.1]

theorem slow_open (α₀ : ℝ) (h : Slow (flow α₀)) :
    ∃ δ > 0, ∀ α, |α - α₀| < δ → Slow (flow α) := by
  obtain ⟨η, hη, hpre, h1, h2, h3⟩ := h
  have hcp : ContinuousOn (fun s => (flow α₀ s).2.1) (Icc 0 η) :=
    (continuous_fst.comp continuous_snd).comp_continuousOn (cont_comp α₀ η)
  have hcq : ContinuousOn (fun s => (flow α₀ s).2.2) (Icc 0 η) :=
    (continuous_snd.comp continuous_snd).comp_continuousOn (cont_comp α₀ η)
  obtain ⟨s1, hs1, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, ⟨le_rfl, hη.le⟩⟩ hcp
  obtain ⟨s2, hs2, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, ⟨le_rfl, hη.le⟩⟩ hcq
  have hM : (flow α₀ s1).2.1 < 1 := (hpre s1 hs1).1
  have hm : 0 < (flow α₀ s2).2.2 := (hpre s2 hs2).2
  set ε := min (min (1 - (flow α₀ s1).2.1) (flow α₀ s2).2.2)
    (min ((3 * (1 - (flow α₀ η).2.1) - (flow α₀ η).2.2) / 4) ((flow α₀ η).1 - 11 / 30)) with hε
  have e1 : ε ≤ 1 - (flow α₀ s1).2.1 := (min_le_left _ _).trans (min_le_left _ _)
  have e2 : ε ≤ (flow α₀ s2).2.2 := (min_le_left _ _).trans (min_le_right _ _)
  have e3 : ε ≤ (3 * (1 - (flow α₀ η).2.1) - (flow α₀ η).2.2) / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have e4 : ε ≤ (flow α₀ η).1 - 11 / 30 := (min_le_right _ _).trans (min_le_right _ _)
  have hε0 : 0 < ε := lt_min (lt_min (by linarith) hm) (lt_min (by linarith) (by linarith))
  obtain ⟨δ, hδ, hcl⟩ := flow_cont η hη.le α₀ hε0
  refine ⟨δ, hδ, fun α hα => ⟨η, hη, ?_, ?_, ?_, ?_⟩⟩
  · intro s hs
    have k := hcl α hα s hs
    have k1 := (dist_c1 (a := flow α s) (b := flow α₀ s)).trans_lt k
    have k2 := (dist_c2 (a := flow α s) (b := flow α₀ s)).trans_lt k
    have := hmax hs; have := hmin hs
    simp only [mem_setOf_eq] at *
    rw [abs_lt] at k1 k2
    constructor <;> linarith
  · -- p is nondecreasing on [0, η] because q > 0 there
    have hq : ∀ s ∈ Icc 0 η, 0 < (flow α s).2.2 := by
      intro s hs
      have k2 := (dist_c2 (a := flow α s) (b := flow α₀ s)).trans_lt (hcl α hα s hs)
      have := hmin hs
      simp only [mem_setOf_eq] at this
      rw [abs_lt] at k2; linarith
    obtain ⟨_, hP, _⟩ := comps α
    have hm := Checked.FalknerSkan.LimitCore.mono hP le_rfl (b := η) (fun x hx => by
      have h := hq x ⟨hx.1.le, hx.2.le⟩
      unfold cl; exact le_max_of_le_right (le_min (by norm_num) h.le))
    have := hm ⟨le_rfl, hη.le⟩ ⟨hη.le, le_rfl⟩ hη.le
    simp only [flow_zero] at this
    exact this
  · have k := hcl α hα η ⟨hη.le, le_rfl⟩
    have k1 := (dist_c1 (a := flow α η) (b := flow α₀ η)).trans_lt k
    have k2 := (dist_c2 (a := flow α η) (b := flow α₀ η)).trans_lt k
    rw [abs_lt] at k1 k2; linarith
  · have k0 := (dist_c0 (a := flow α η) (b := flow α₀ η)).trans_lt (hcl α hα η ⟨hη.le, le_rfl⟩)
    rw [abs_lt] at k0; linarith

theorem slow_not_over {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 11 / 10) (hS : Slow (flow α))
    (hO : Over (flow α)) : False := by
  obtain ⟨hF, hP, hQ⟩ := comps α
  obtain ⟨η₀, hη₀, hpre, hs1, hs2, hs3⟩ := hS
  have U := Work.FSNeg.NUnclamp.unclamp hα0 hα1 hF hP hQ (by simp [flow_zero]) (by simp [flow_zero])
    (by simp [flow_zero]) hη₀ hpre hs1 hs2 hs3
  obtain ⟨η, hη, hp⟩ := hO
  have := (U η hη.le).2.1
  linarith

/-- Neither event: the flow is a solution of the scaled problem in the decay class. -/
theorem neither_class {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 11 / 10) (hnS : ¬ Slow (flow α))
    (hnO : ¬ Over (flow α)) :
    let F := fun t => (flow α t).1
    let P := fun t => (flow α t).2.1
    let Q := fun t => (flow α t).2.2
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt F (P η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt P (Q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(10 * F η * Q η) + 1 - P η ^ 2) (Ici 0) η) ∧
    Tendsto P atTop (𝓝 1) ∧ (∀ η ∈ Ici (0 : ℝ), 0 < Q η) ∧
    (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - P η) ≤ Q η) := by
  intro F P Q
  obtain ⟨hF, hP, hQ⟩ := comps α
  have h0 := flow_zero α
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
    have hZd : ∀ t ∈ Icc 0 τ, HasDerivWithinAt Z (vN t (Z t)) (Icc 0 τ) t := by
      intro t _
      have hv : vN t (Z t) = (1, 0, 0) := by
        simp only [hZ, vN]
        rw [Work.FSNeg.NUnclamp.cl_eq (c := 2) (y := 1) (by norm_num) (by norm_num),
          Work.FSNeg.NUnclamp.cl_eq (c := 2) (y := 0) (by norm_num) (by norm_num)]
        simp
      rw [hv]
      have a1 : HasDerivWithinAt (fun t => F τ + (t - τ)) 1 (Icc 0 τ) t :=
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
    simp only [hZ, h0] at h2
    norm_num at h2
  have U := Work.FSNeg.NUnclamp.unclamp_neither hα0 hα1 hF hP hQ hF0 hP0 hQ0 hp1 htouch
  have ceq := @Work.FSNeg.NUnclamp.cl_eq
  have tF : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt F (P η) (Ici 0) η := fun η hη => by
    have u := U η hη
    have := hF η hη; rwa [ceq (by linarith [u.1]) (by linarith [u.2.1])] at this
  have tP : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt P (Q η) (Ici 0) η := fun η hη => by
    have u := U η hη
    have := hP η hη; rwa [ceq (by linarith [u.2.2.1]) (by linarith [u.2.2.2.1])] at this
  have tQ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(10 * F η * Q η) + 1 - P η ^ 2) (Ici 0) η :=
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
    Work.FSNeg.NLimit.neg_limit (by norm_num : (0 : ℝ) < 10) tF tP tQ le_rfl
      hqpos (by rw [hP0]; norm_num) hplt
  have hft := Work.FSNeg.NLimit.f_tendsto tF hlim
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hft.eventually_gt_atTop (11 / 30))
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
  exact Work.FSNeg.NRiccati.riccati_up (by norm_num : (0 : ℝ) < 10) (by norm_num : (0 : ℝ) < 3)
    tP tQ ha0 (fun η hη => hplt η (ha0.trans hη)) hft hlow

theorem core_exists (hS : ChainTo (3 / 4) Slow) (hO : ChainTo (11 / 10) Over) :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / 10) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q η) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) := by
  set lo : ℝ := 3 / 4 with hlo
  set hi : ℝ := 11 / 10 with hhi
  have hlh : lo < hi := by rw [hlo, hhi]; norm_num
  have hlo0 : (0 : ℝ) < lo := by rw [hlo]; norm_num
  have hhi1 : hi ≤ 11 / 10 := by rw [hhi]
  have slow_lo : Slow (flow lo) := of_chain hS
  have over_hi : Over (flow hi) := of_chain hO
  clear_value lo hi
  set S : Set ℝ := {α | α ∈ Icc lo hi ∧ Slow (flow α)} with hSd
  have hloS : lo ∈ S := ⟨⟨le_rfl, hlh.le⟩, slow_lo⟩
  have hne : S.Nonempty := ⟨lo, hloS⟩
  have hbdd : BddAbove S := ⟨hi, fun α hα => hα.1.2⟩
  set a := sSup S with ha
  have hloa := le_csSup hbdd hloS
  obtain ⟨δ2, hδ2, hO2⟩ := over_open hi over_hi
  have ha_lt : a < hi := by
    have hub : ∀ α ∈ S, α ≤ hi - δ2 / 2 := by
      intro α hα
      by_contra hc
      push Not at hc
      have hOα := hO2 α (by rw [abs_lt]; constructor <;> linarith [hα.1.2])
      exact slow_not_over (by linarith [hα.1.1]) (by linarith [hα.1.2]) hα.2 hOα
    have := csSup_le hne hub
    linarith
  have hnS : ¬ Slow (flow a) := by
    intro hSa
    obtain ⟨δ, hδ, hSa'⟩ := slow_open a hSa
    obtain ⟨α', hα'd⟩ : ∃ x : ℝ, x = a + min (δ / 2) ((hi - a) / 2) := ⟨_, rfl⟩
    have h1 : 0 < min (δ / 2) ((hi - a) / 2) := lt_min (by linarith) (by linarith)
    have h2 : min (δ / 2) ((hi - a) / 2) ≤ δ / 2 := min_le_left _ _
    have h3 : min (δ / 2) ((hi - a) / 2) ≤ (hi - a) / 2 := min_le_right _ _
    have hα'S : α' ∈ S := ⟨⟨by linarith, by linarith⟩,
      hSa' α' (by rw [abs_lt]; constructor <;> linarith)⟩
    have := le_csSup hbdd hα'S
    linarith
  have hnO : ¬ Over (flow a) := by
    intro hOa
    obtain ⟨δ, hδ, hOa'⟩ := over_open a hOa
    obtain ⟨α, hαS, hαa⟩ := exists_lt_of_lt_csSup hne (show a - δ < a by linarith)
    have hle : α ≤ a := le_csSup hbdd hαS
    exact slow_not_over (by linarith [hαS.1.1]) (by linarith [hαS.1.2]) hαS.2
      (hOa' α (by rw [abs_lt]; constructor <;> linarith))
  obtain ⟨tF, tP, tQ, hlim, hqpos, hdec⟩ :=
    neither_class (by linarith) (by linarith) hnS hnO
  set F := fun t => (flow a t).1
  set P := fun t => (flow a t).2.1
  set Q := fun t => (flow a t).2.2
  have hF0 : F 0 = 0 := by simp [F, flow_zero]
  have hP0 : P 0 = 0 := by simp [P, flow_zero]
  have hc : 0 < Real.sqrt 10 := Real.sqrt_pos.2 (by norm_num)
  have hc2 : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have tQ' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(10 * F η * Q η) - (-1) * (1 - P η ^ 2)) (Ici 0) η :=
    fun η hη => (tQ η hη).congr_deriv (by ring)
  obtain ⟨A, B, C⟩ := Checked.FalknerSkan.FSScale.scale hc tF tP tQ'
  have hm := Checked.FalknerSkan.FSScale.mapsTo_div hc
  refine ⟨fun s => Real.sqrt 10 * F (s / Real.sqrt 10), fun s => P (s / Real.sqrt 10),
    fun s => Q (s / Real.sqrt 10) / Real.sqrt 10, A, B, fun s hs => ?_, by simp [hF0],
    by simp [hP0], Checked.FalknerSkan.FSScale.scale_lim hc hlim,
    fun s hs => div_pos (hqpos _ (hm hs)) hc, fun M => ?_⟩
  · refine (C s hs).congr_deriv ?_
    field_simp
    rw [hc2]
  · have hd := (tendsto_id.atTop_div_const hc).eventually (hdec (M * Real.sqrt 10))
    filter_upwards [hd] with s hs
    simp only [id] at hs
    rw [le_div_iff₀ hc]
    linarith

end Work.FSNeg.NAssemble
