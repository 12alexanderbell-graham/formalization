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
import Checked.FalknerSkan.LimitCore
import Checked.FSSep.UCrocco
import Checked.FalknerSkan.NegNoCross
import Checked.FalknerSkan.NegCore

/-! Falkner–Skan separation, comparison of two zero-wall-value solutions with different pressure-gradient parameters in Crocco variables: order at the wall, no crossing, and the first step of the tail estimate. Module `UCompare`, promoted from `Work/FSSep/UCompare.lean`. -/

namespace Checked.FSSep.UCompare
open Set Filter Topology
open Checked.FalknerSkan.LimitCore

/-- One β-form solution with zero wall shear in the monotone class. -/
structure SolB (β : ℝ) (f p q : ℝ → ℝ) : Prop where
  hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η
  hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η
  hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η
  hf0 : f 0 = 0
  hp0 : p 0 = 0
  hq0 : q 0 = 0
  hlim : Tendsto p atTop (𝓝 1)
  hpos : ∀ η ∈ Ioi (0 : ℝ), 0 < q η

theorem SolB.smono {β : ℝ} {f p q : ℝ → ℝ} (S : SolB β f p q) : StrictMonoOn p (Ici 0) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0)
  · intro x hx; exact (S.hp x hx).continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    exact (S.hp x (Set.mem_Ici.2 (le_of_lt hx))).mono interior_subset
  · intro x hx
    rw [interior_Ici] at hx
    exact S.hpos x hx

theorem SolB.bounds {β : ℝ} {f p q : ℝ → ℝ} (S : SolB β f p q) :
    ∀ η ∈ Ici (0 : ℝ), 0 ≤ p η ∧ p η < 1 := by
  have hm := S.smono
  intro η hη
  have hη0 : (0 : ℝ) ≤ η := hη
  refine ⟨?_, ?_⟩
  · have := hm.monotoneOn (Set.mem_Ici.2 le_rfl) hη hη0
    rwa [S.hp0] at this
  · have h1 : p η < p (η + 1) := hm hη (show (0 : ℝ) ≤ η + 1 by linarith) (by linarith)
    have h2 : p (η + 1) ≤ 1 := by
      apply ge_of_tendsto S.hlim
      rw [eventually_atTop]
      refine ⟨η + 1, fun s hs => ?_⟩
      exact hm.monotoneOn (show (0 : ℝ) ≤ η + 1 by linarith) (show (0 : ℝ) ≤ s by linarith) hs
    linarith

theorem SolB.reach {β : ℝ} {f p q : ℝ → ℝ} (S : SolB β f p q) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ∃ u ∈ Ici (0 : ℝ), p u = s := by
  obtain ⟨R, hR⟩ := (S.hlim.eventually (lt_mem_nhds hs1)).exists_forall_of_atTop
  set R' := max R 0
  have hR' : s < p R' := hR R' (le_max_left _ _)
  have hc : ContinuousOn p (Icc 0 R') := cont_of S.hp le_rfl
  obtain ⟨u, hu, hpu⟩ := intermediate_value_Icc (le_max_right R 0) hc
    (show s ∈ Icc (p 0) (p R') by rw [S.hp0]; exact ⟨hs0, hR'.le⟩)
  exact ⟨u, hu.1, hpu⟩

theorem SolB.small {β : ℝ} {f p q : ℝ → ℝ} (S : SolB β f p q) {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) :
    ∃ η ∈ Ici T, q η < ε := by
  by_contra hcon
  push Not at hcon
  have hmono : ∀ η ∈ Ici T, p T + ε * (η - T) ≤ p η := by
    intro η hη
    have hg : ∀ x ∈ Ici (0 : ℝ),
        HasDerivWithinAt (fun y => p y - ε * y) (q x - ε * 1) (Ici 0) x := fun x hx =>
      (S.hp x hx).sub ((hasDerivWithinAt_id x _).const_mul ε)
    have hm := mono hg hT (b := η) (fun x hx => by
      have := hcon x hx.1.le
      linarith)
    have := hm ⟨le_refl T, hη⟩ ⟨hη, le_refl η⟩ hη
    simp only at this
    nlinarith
  have hpos' : 0 ≤ T + 1 / ε := by positivity
  have hb := S.bounds (T + 1 / ε) hpos'
  have hinv : 0 < 1 / ε := by positivity
  have := hmono (T + 1 / ε) (mem_Ici.2 (by linarith))
  have h1 : ε * (T + 1 / ε - T) = 1 := by field_simp; ring
  have h2 := (S.bounds T hT).1
  linarith [hb.2]

/-- The pressure-gradient parameter of a zero-wall-shear solution in the class is negative. -/
theorem SolB.beta_neg {β : ℝ} {f p q : ℝ → ℝ} (S : SolB β f p q) : β < 0 := by
  rcases lt_trichotomy β 0 with h | h | h
  · exact h
  · exfalso
    subst h
    have key := Checked.FalknerSkan.NegCore.eq_of_startb (β := 0) S.hf S.hp S.hq
      (f₂ := fun _ => 0) (p₂ := fun _ => 0) (q₂ := fun _ => 0)
      (fun η _ => (hasDerivWithinAt_const η (Ici 0) (0 : ℝ)))
      (fun η _ => (hasDerivWithinAt_const η (Ici 0) (0 : ℝ)))
      (fun η _ => (hasDerivWithinAt_const η (Ici 0) (0 : ℝ)).congr_deriv (by ring))
      S.hf0 S.hp0 S.hq0
    have h1 : q 1 = 0 := (key 1 (by norm_num)).2.2
    have h2 := S.hpos 1 (by norm_num)
    linarith
  · exfalso
    have hd := S.hq 0 (mem_Ici.2 le_rfl)
    have := right_nonneg hd (by
      filter_upwards [self_mem_nhdsWithin] with y hy
      rw [S.hq0]; exact (S.hpos y hy).le)
    rw [S.hf0, S.hp0, S.hq0] at this
    linarith

/-- The start at zero wall shear: w = z² has w' → −2β at t = 0, so the curve with the smaller β
lies above near t = 0. -/
theorem start {L βA βB : ℝ} (hβ : βA < βB) (hL : 0 < L) {zA zB FA FB : ℝ → ℝ}
    (hzA : ∀ t ∈ Ioo 0 L, 0 < zA t) (hzB : ∀ t ∈ Ioo 0 L, 0 < zB t)
    (czA : ContinuousOn zA (Ico 0 L)) (czB : ContinuousOn zB (Ico 0 L))
    (cFA : ContinuousOn FA (Ico 0 L)) (cFB : ContinuousOn FB (Ico 0 L))
    (dzA : ∀ t ∈ Ioo 0 L, HasDerivAt zA (-(FA t) - βA * (1 - t ^ 2) / zA t) t)
    (dzB : ∀ t ∈ Ioo 0 L, HasDerivAt zB (-(FB t) - βB * (1 - t ^ 2) / zB t) t)
    (hzA0 : zA 0 = 0) (hzB0 : zB 0 = 0) :
    ∃ δ > 0, δ < L ∧ ∀ t ∈ Ioc 0 δ, zB t < zA t := by
  set g : ℝ → ℝ := fun t =>
    -(2 * zA t * FA t) + 2 * zB t * FB t + 2 * (βB - βA) * (1 - t ^ 2) with hg
  have cg : ContinuousOn g (Ico 0 L) := by
    have c1 : ContinuousOn (fun t : ℝ => (1 : ℝ) - t ^ 2) (Ico 0 L) := by fun_prop
    exact ((((continuousOn_const.mul czA).mul cFA).neg).add
      ((continuousOn_const.mul czB).mul cFB)).add (continuousOn_const.mul c1)
  have hg0 : 0 < g 0 := by
    simp only [hg, hzA0, hzB0]; nlinarith
  have hev : ∀ᶠ t in 𝓝[Ico 0 L] (0 : ℝ), 0 < g t :=
    (cg 0 ⟨le_rfl, hL⟩).tendsto.eventually (lt_mem_nhds hg0)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hεg⟩ := hev
  set δ := min (ε / 2) (L / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδL : δ < L := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hsub : Icc 0 δ ⊆ Ico 0 L := fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hδL⟩
  have hW : StrictMonoOn (fun t => zA t * zA t - zB t * zB t) (Icc 0 δ) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (f' := g) (convex_Icc 0 δ)
    · exact ((czA.mono hsub).mul (czA.mono hsub)).sub ((czB.mono hsub).mul (czB.mono hsub))
    · intro t ht
      rw [interior_Icc] at ht
      have htL : t ∈ Ioo 0 L := ⟨ht.1, lt_trans ht.2 hδL⟩
      have hA := (hzA t htL).ne'
      have hB := (hzB t htL).ne'
      have := ((dzA t htL).mul (dzA t htL)).sub ((dzB t htL).mul (dzB t htL))
      refine (this.congr_deriv ?_).hasDerivWithinAt
      simp only [hg]
      field_simp
      ring
    · intro t ht
      rw [interior_Icc] at ht
      refine hεg ?_ ⟨ht.1.le, lt_trans ht.2 hδL⟩
      rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
      exact lt_trans ht.2 hδε
  refine ⟨δ, hδ0, hδL, fun t ht => ?_⟩
  have := hW ⟨le_rfl, hδ0.le⟩ ⟨ht.1.le, ht.2⟩ ht.1
  simp only [hzA0, hzB0] at this
  have hA := hzA t ⟨ht.1, lt_of_le_of_lt ht.2 hδL⟩
  have hB := hzB t ⟨ht.1, lt_of_le_of_lt ht.2 hδL⟩
  nlinarith

/-- No crossing after the start: zB < zA on the whole common range (L ≤ 1). -/
theorem no_cross_s {L βA βB : ℝ} (hβ : βA < βB) (hL1 : L ≤ 1) {zA zB FA FB : ℝ → ℝ}
    (hzA : ∀ t ∈ Ioo 0 L, 0 < zA t) (hzB : ∀ t ∈ Ioo 0 L, 0 < zB t)
    (czA : ContinuousOn zA (Ico 0 L)) (czB : ContinuousOn zB (Ico 0 L))
    (cFA : ContinuousOn FA (Ico 0 L)) (cFB : ContinuousOn FB (Ico 0 L))
    (dFA : ∀ t ∈ Ioo 0 L, HasDerivAt FA (t / zA t) t)
    (dFB : ∀ t ∈ Ioo 0 L, HasDerivAt FB (t / zB t) t)
    (dzA : ∀ t ∈ Ioo 0 L, HasDerivAt zA (-(FA t) - βA * (1 - t ^ 2) / zA t) t)
    (dzB : ∀ t ∈ Ioo 0 L, HasDerivAt zB (-(FB t) - βB * (1 - t ^ 2) / zB t) t)
    (hzA0 : zA 0 = 0) (hzB0 : zB 0 = 0) (hF0 : FA 0 = FB 0) :
    ∀ t ∈ Ioo 0 L, zB t < zA t := by
  intro t₁ ht₁
  have hL : 0 < L := lt_trans ht₁.1 ht₁.2
  obtain ⟨δ, hδ0, hδL, hst⟩ := start hβ hL hzA hzB czA czB cFA cFB dzA dzB hzA0 hzB0
  by_contra hneg
  rw [not_lt] at hneg
  have hδt : δ < t₁ := by
    by_contra hc; push Not at hc
    have := hst t₁ ⟨ht₁.1, hc⟩; linarith
  set D : ℝ → ℝ := fun t => zA t - zB t with hD
  set S : Set ℝ := Icc δ t₁ ∩ D ⁻¹' Iic 0 with hS
  have hsub : Icc δ t₁ ⊆ Ico 0 L := fun t ht => ⟨hδ0.le.trans ht.1, lt_of_le_of_lt ht.2 ht₁.2⟩
  have hSc : IsClosed S :=
    ((czA.mono hsub).sub (czB.mono hsub)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSne : S.Nonempty := ⟨t₁, ⟨hδt.le, le_refl t₁⟩, show zA t₁ - zB t₁ ≤ 0 by linarith⟩
  have hSbdd : BddBelow S := ⟨δ, fun t ht => ht.1.1⟩
  set τ := sInf S with hτdef
  have hτ : τ ∈ S := hSc.csInf_mem hSne hSbdd
  have hDτ : D τ ≤ 0 := hτ.2
  have hτL : τ < L := lt_of_le_of_lt hτ.1.2 ht₁.2
  have hδτ : δ < τ := by
    rcases eq_or_lt_of_le hτ.1.1 with h | h
    · exfalso
      rw [← h] at hDτ
      have := hst δ ⟨hδ0, le_rfl⟩
      simp only [hD] at hDτ
      linarith
    · exact h
  have hτ0 : 0 < τ := lt_trans hδ0 hδτ
  have hbefore : ∀ t ∈ Ioo 0 τ, 0 < D t := by
    intro t ht
    rcases le_or_gt t δ with h | h
    · have := hst t ⟨ht.1, h⟩; simp only [hD]; linarith
    · by_contra hc
      rw [not_lt] at hc
      have htS : t ∈ S := ⟨⟨h.le, le_trans ht.2.le hτ.1.2⟩, hc⟩
      have := csInf_le hSbdd htS
      linarith [ht.2]
  have hτI : τ ∈ Ioo 0 L := ⟨hτ0, hτL⟩
  have hDcA : ContinuousAt D τ :=
    ((czA.sub czB) τ ⟨hτ0.le, hτL⟩).continuousAt (Ico_mem_nhds hτ0 hτL)
  have hDτ0 : D τ = 0 := by
    have hge : 0 ≤ D τ := by
      refine ge_of_tendsto (hDcA.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio τ))) ?_
      filter_upwards [Ioo_mem_nhdsLT hτ0] with y hy
      exact (hbefore y hy).le
    linarith
  have hzeq : zA τ = zB τ := by
    simp only [hD] at hDτ0
    linarith
  -- E = FB − FA is nondecreasing on [0, τ], so E(τ) ≥ 0
  have hsubτ : Icc 0 τ ⊆ Ico 0 L := fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hτL⟩
  have hEm : MonotoneOn (fun t => FB t - FA t) (Icc 0 τ) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => t / zB t - t / zA t)
      (convex_Icc 0 τ) ((cFB.mono hsubτ).sub (cFA.mono hsubτ))
    · intro t ht
      rw [interior_Icc] at ht
      have htL : t ∈ Ioo 0 L := ⟨ht.1, lt_trans ht.2 hτL⟩
      exact ((dFB t htL).sub (dFA t htL)).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have htL : t ∈ Ioo 0 L := ⟨ht.1, lt_trans ht.2 hτL⟩
      have h1 : 0 < zB t := hzB t htL
      have h2 := hbefore t ht
      simp only [hD] at h2
      have : t / zA t ≤ t / zB t := div_le_div_of_nonneg_left ht.1.le h1 (by linarith)
      linarith
  have hEτ : 0 ≤ FB τ - FA τ := by
    have := hEm ⟨le_rfl, hτ0.le⟩ ⟨hτ0.le, le_rfl⟩ hτ0.le
    simp only at this
    rw [hF0] at this
    linarith
  have hDd : HasDerivAt D
      ((-(FA τ) - βA * (1 - τ ^ 2) / zA τ) - (-(FB τ) - βB * (1 - τ ^ 2) / zB τ)) τ :=
    (dzA τ hτI).sub (dzB τ hτI)
  have hzτ : 0 < zB τ := hzB τ hτI
  have h1τ : 0 < 1 - τ ^ 2 := by nlinarith
  have hdpos : 0 < (-(FA τ) - βA * (1 - τ ^ 2) / zA τ) - (-(FB τ) - βB * (1 - τ ^ 2) / zB τ) := by
    rw [hzeq]
    have : 0 < (βB - βA) * (1 - τ ^ 2) / zB τ := by
      apply div_pos (mul_pos (by linarith) h1τ) hzτ
    have e : (-(FA τ) - βA * (1 - τ ^ 2) / zB τ) - (-(FB τ) - βB * (1 - τ ^ 2) / zB τ)
        = (FB τ - FA τ) + (βB - βA) * (1 - τ ^ 2) / zB τ := by ring
    rw [e]; linarith
  have hleft := left_neg hDd hdpos hDτ0
  obtain ⟨y, hy1, hy2⟩ := (hleft.and (Ioo_mem_nhdsLT hτ0)).exists
  have := hbefore y hy2
  linarith

/-- Step 1 of Theorem U′ for two different β (the Crocco side). -/
theorem stepS {L βA βB t₀ t : ℝ} (hβA : βA ≤ 0) (hβB : βB ≤ 0) (hL : L ≤ 1) (ht₀ : 0 < t₀)
    (ht : t₀ ≤ t) (htL : t < L) {zA zB FA FB G : ℝ → ℝ}
    (hzA : ∀ s ∈ Ioo 0 L, 0 < zA s) (hzB : ∀ s ∈ Ioo 0 L, 0 < zB s)
    (czA : ContinuousOn zA (Ico 0 L)) (czB : ContinuousOn zB (Ico 0 L))
    (cG : ContinuousOn G (Ico 0 L))
    (dzA : ∀ s ∈ Ioo 0 L, HasDerivAt zA (-(FA s) - βA * (1 - s ^ 2) / zA s) s)
    (dzB : ∀ s ∈ Ioo 0 L, HasDerivAt zB (-(FB s) - βB * (1 - s ^ 2) / zB s) s)
    (dG : ∀ s ∈ Ioo 0 L, HasDerivAt G ((1 - s) / zB s) s)
    (hE : MonotoneOn (fun s => FB s - FA s) (Ico 0 L)) (hD : zB t₀ ≤ zA t₀) :
    (FB t₀ - FA t₀) * (t - t₀) ≤ zA t - zB t + 2 * (-βB) * (G t - G t₀) := by
  have hsub : Icc t₀ t ⊆ Ico 0 L := fun s hs => ⟨ht₀.le.trans hs.1, lt_of_le_of_lt hs.2 htL⟩
  set c := FB t₀ - FA t₀ with hc
  set Ψ : ℝ → ℝ := fun s => (zA s - zB s) + 2 * (-βB) * G s - c * s with hΨ
  have hmono : MonotoneOn Ψ (Icc t₀ t) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun s => ((-(FA s) - βA * (1 - s ^ 2) / zA s) - (-(FB s) - βB * (1 - s ^ 2) / zB s))
        + 2 * (-βB) * ((1 - s) / zB s) - c)
      (convex_Icc t₀ t)
    · exact (((czA.mono hsub).sub (czB.mono hsub)).add
        (continuousOn_const.mul (cG.mono hsub))).sub
        ((continuous_const.mul continuous_id).continuousOn)
    · intro s hs
      rw [interior_Icc] at hs
      have hsI : s ∈ Ioo 0 L := ⟨ht₀.trans hs.1, lt_trans hs.2 htL⟩
      have := (((dzA s hsI).sub (dzB s hsI)).add ((dG s hsI).const_mul (2 * (-βB)))).sub
        ((hasDerivAt_id s).const_mul c)
      refine (this.congr_deriv ?_).hasDerivWithinAt
      simp
    · intro s hs
      rw [interior_Icc] at hs
      have hs0 : 0 < s := ht₀.trans hs.1
      have hsL : s < L := lt_trans hs.2 htL
      have h1 : 0 < zA s := hzA s ⟨hs0, hsL⟩
      have h2 : 0 < zB s := hzB s ⟨hs0, hsL⟩
      have hs1 : s < 1 := lt_of_lt_of_le hsL hL
      have hEs : FB t₀ - FA t₀ ≤ FB s - FA s :=
        hE ⟨ht₀.le, lt_of_le_of_lt ht htL⟩ ⟨hs0.le, hsL⟩ hs.1.le
      have key : (-(βA * (1 - s ^ 2) / zA s)) + βB * (1 - s ^ 2) / zB s
          + 2 * (-βB) * ((1 - s) / zB s)
          = (-βA) * (1 - s ^ 2) / zA s + (-βB) * (1 - s) ^ 2 / zB s := by
        field_simp
        ring
      have hnn : 0 ≤ (-βA) * (1 - s ^ 2) / zA s + (-βB) * (1 - s) ^ 2 / zB s := by
        have : 0 ≤ 1 - s ^ 2 := by nlinarith
        have a1 : 0 ≤ (-βA) * (1 - s ^ 2) / zA s :=
          div_nonneg (mul_nonneg (by linarith) this) h1.le
        have a2 : 0 ≤ (-βB) * (1 - s) ^ 2 / zB s :=
          div_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) h2.le
        linarith
      have : ((-(FA s) - βA * (1 - s ^ 2) / zA s) - (-(FB s) - βB * (1 - s ^ 2) / zB s))
          + 2 * (-βB) * ((1 - s) / zB s) - c
          = (FB s - FA s - c) + ((-(βA * (1 - s ^ 2) / zA s)) + βB * (1 - s ^ 2) / zB s
            + 2 * (-βB) * ((1 - s) / zB s)) := by ring
      rw [this, key]
      linarith
  have h := hmono ⟨le_refl t₀, ht⟩ ⟨ht, le_refl t⟩ ht
  simp only [hΨ] at h
  have : c * (t - t₀) = c * t - c * t₀ := by ring
  rw [this]
  linarith

end Checked.FSSep.UCompare
