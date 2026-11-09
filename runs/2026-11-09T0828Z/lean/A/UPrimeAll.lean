import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Checked.FalknerSkan.LimitCore
/-! Scratch (run 2026-11-09T0828Z, fork A): Crocco map for the adverse pressure sign. -/

namespace Scratch.NegCrocco
open Set

/-- The Crocco change of variables t = p(η), pressure term `+ 1 - p²` (β < 0 after scaling). -/
theorem crocco_pos {k E : ℝ} (hE : 0 < E) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Icc 0 E, HasDerivWithinAt f (p η) (Icc 0 E) η)
    (hp : ∀ η ∈ Icc 0 E, HasDerivWithinAt p (q η) (Icc 0 E) η)
    (hq : ∀ η ∈ Icc 0 E, HasDerivWithinAt q (-(k * f η * q η) + 1 - p η ^ 2) (Icc 0 E) η)
    (hp0 : p 0 = 0) (hpos : ∀ η ∈ Ico 0 E, 0 < q η) :
    ∃ ψ : ℝ → ℝ,
      (∀ t ∈ Ico 0 (p E), ψ t ∈ Ico 0 E ∧ p (ψ t) = t) ∧
      (∀ η ∈ Ico 0 E, ψ (p η) = η) ∧
      ContinuousOn (fun t => q (ψ t)) (Ico 0 (p E)) ∧
      ContinuousOn (fun t => f (ψ t)) (Ico 0 (p E)) ∧
      (∀ t ∈ Ioo 0 (p E), HasDerivAt (fun s => f (ψ s)) (t / q (ψ t)) t) ∧
      (∀ t ∈ Ioo 0 (p E), HasDerivAt (fun s => q (ψ s)) (-(k * f (ψ t)) + (1 - t ^ 2) / q (ψ t)) t) ∧
      ContinuousOn ψ (Ico 0 (p E)) ∧
      (∀ t ∈ Ioo 0 (p E), HasDerivAt ψ (q (ψ t))⁻¹ t) := by
  have hfc : ContinuousOn f (Icc 0 E) := fun x hx => (hf x hx).continuousWithinAt
  have hpc : ContinuousOn p (Icc 0 E) := fun x hx => (hp x hx).continuousWithinAt
  have hqc : ContinuousOn q (Icc 0 E) := fun x hx => (hq x hx).continuousWithinAt
  -- interior derivatives
  have hpA : ∀ x ∈ Ioo 0 E, HasDerivAt p (q x) x := fun x hx =>
    (hp x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
  have hfA : ∀ x ∈ Ioo 0 E, HasDerivAt f (p x) x := fun x hx =>
    (hf x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
  have hqA : ∀ x ∈ Ioo 0 E, HasDerivAt q (-(k * f x * q x) + 1 - p x ^ 2) x := fun x hx =>
    (hq x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
  have hmono : StrictMonoOn p (Icc 0 E) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 E) hpc
    intro x hx
    rw [interior_Icc] at hx
    rw [(hpA x hx).deriv]
    exact hpos x ⟨hx.1.le, hx.2⟩
  have hE0 : (0 : ℝ) ≤ E := hE.le
  have hpE : 0 < p E := by
    have := hmono ⟨le_rfl, hE0⟩ ⟨hE0, le_rfl⟩ hE
    rwa [hp0] at this
  have hsurj : ∀ t ∈ Icc 0 (p E), ∃ η ∈ Icc 0 E, p η = t := by
    intro t ht
    rw [← hp0] at ht
    exact intermediate_value_Icc hE0 hpc ht
  set ψ := Function.invFunOn p (Icc 0 E) with hψdef
  have hψ : ∀ t ∈ Icc 0 (p E), ψ t ∈ Icc 0 E ∧ p (ψ t) = t := fun t ht =>
    Function.invFunOn_pos (hsurj t ht)
  have hψp : ∀ η ∈ Icc 0 E, ψ (p η) = η := fun η hη =>
    hmono.injOn.leftInvOn_invFunOn hη
  have hψ' : ∀ t ∈ Ico 0 (p E), ψ t ∈ Ico 0 E ∧ p (ψ t) = t := by
    intro t ht
    obtain ⟨h1, h2⟩ := hψ t (Ico_subset_Icc_self ht)
    refine ⟨⟨h1.1, lt_of_le_of_ne h1.2 ?_⟩, h2⟩
    intro h
    rw [h] at h2
    exact absurd h2 (ne_of_gt ht.2)
  have hψi : ∀ t ∈ Ioo 0 (p E), ψ t ∈ Ioo 0 E := by
    intro t ht
    obtain ⟨⟨h1, h2⟩, h3⟩ := hψ' t (Ioo_subset_Ico_self ht)
    refine ⟨lt_of_le_of_ne h1 ?_, h2⟩
    intro h
    rw [← h, hp0] at h3
    exact absurd h3 (ne_of_lt ht.1)
  have hψmono : MonotoneOn ψ (Icc 0 (p E)) := by
    intro a ha b hb hab
    obtain ⟨ha1, ha2⟩ := hψ a ha
    obtain ⟨hb1, hb2⟩ := hψ b hb
    rw [← hmono.le_iff_le ha1 hb1, ha2, hb2]
    exact hab
  have himg : Icc 0 E ⊆ ψ '' Icc 0 (p E) := by
    intro η hη
    refine ⟨p η, ⟨?_, ?_⟩, hψp η hη⟩
    · rw [← hp0]; exact hmono.monotoneOn ⟨le_rfl, hE0⟩ hη hη.1
    · exact hmono.monotoneOn hη ⟨hE0, le_rfl⟩ hη.2
  have hψ0 : ψ 0 = 0 := by
    have := hψp 0 ⟨le_rfl, hE0⟩
    rwa [hp0] at this
  have hψcA : ∀ t ∈ Ioo 0 (p E), ContinuousAt ψ t := by
    intro t ht
    have hi := hψi t ht
    apply continuousAt_of_monotoneOn_of_image_mem_nhds hψmono
      (Icc_mem_nhds ht.1 ht.2)
    exact Filter.mem_of_superset (Icc_mem_nhds hi.1 hi.2) himg
  have hψc : ContinuousOn ψ (Ico 0 (p E)) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h
      have : ContinuousWithinAt ψ (Ici 0) 0 := by
        apply continuousWithinAt_right_of_monotoneOn_of_image_mem_nhdsWithin hψmono
          (Icc_mem_nhdsGE hpE)
        rw [hψ0]
        exact Filter.mem_of_superset (Icc_mem_nhdsGE hE) himg
      exact this.mono Ico_subset_Ici_self
    · exact (hψcA t ⟨h, ht.2⟩).continuousWithinAt
  have hmaps : MapsTo ψ (Ico 0 (p E)) (Icc 0 E) := fun t ht =>
    Ico_subset_Icc_self (hψ' t ht).1
  have hψD : ∀ t ∈ Ioo 0 (p E), HasDerivAt ψ (q (ψ t))⁻¹ t := by
    intro t ht
    have hi := hψi t ht
    apply HasDerivAt.of_local_left_inverse (hψcA t ht) (hpA _ hi)
      (hpos _ (Ioo_subset_Ico_self hi)).ne'
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with y hy
    exact (hψ' y (Ioo_subset_Ico_self hy)).2
  refine ⟨ψ, hψ', fun η hη => hψp η (Ico_subset_Icc_self hη),
    hqc.comp hψc hmaps, hfc.comp hψc hmaps, ?_, ?_, hψc, hψD⟩
  · intro t ht
    have hi := hψi t ht
    have hqne := (hpos _ (Ioo_subset_Ico_self hi)).ne'
    have := (hfA _ hi).comp t (hψD t ht)
    refine this.congr_deriv ?_
    rw [(hψ' t (Ioo_subset_Ico_self ht)).2]
    field_simp
  · intro t ht
    have hi := hψi t ht
    have hqne := (hpos _ (Ioo_subset_Ico_self hi)).ne'
    have := (hqA _ hi).comp t (hψD t ht)
    refine this.congr_deriv ?_
    rw [(hψ' t (Ioo_subset_Ico_self ht)).2]
    field_simp
    ring

end Scratch.NegCrocco



/-! Scratch (run 2026-11-09T0828Z, fork A): Lemma T of the β < 0 research note
(`runs/2026-11-09T0428Z/research/fs_negative_beta.md` §2) — no crossing of two Crocco curves of
the adverse-pressure system z' = −K F + (1 − t²)/z, F' = t/z. -/

namespace Scratch.NoCross
open Set Filter Topology

/-- On a window [0, s] where z₁ ≤ z₂ inside, E = F₁ − F₂ is monotone. -/
theorem E_mono {L s : ℝ} {z₁ z₂ F₁ F₂ : ℝ → ℝ}
    (hz₁ : ∀ t ∈ Ico 0 L, 0 < z₁ t)
    (cF₁ : ContinuousOn F₁ (Ico 0 L)) (cF₂ : ContinuousOn F₂ (Ico 0 L))
    (dF₁ : ∀ t ∈ Ioo 0 L, HasDerivAt F₁ (t / z₁ t) t)
    (dF₂ : ∀ t ∈ Ioo 0 L, HasDerivAt F₂ (t / z₂ t) t)
    (hsL : s < L) (hle : ∀ t ∈ Ioo 0 s, z₁ t ≤ z₂ t) :
    MonotoneOn (fun t => F₁ t - F₂ t) (Icc 0 s) := by
  have hsub : Icc 0 s ⊆ Ico 0 L := fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hsL⟩
  have hsubI : Ioo 0 s ⊆ Ioo 0 L := fun t ht => ⟨ht.1, lt_trans ht.2 hsL⟩
  apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => t / z₁ t - t / z₂ t)
    (convex_Icc 0 s) ((cF₁.mono hsub).sub (cF₂.mono hsub))
  · intro t ht
    rw [interior_Icc] at ht
    exact ((dF₁ t (hsubI ht)).sub (dF₂ t (hsubI ht))).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    have h1 : 0 < z₁ t := hz₁ t ⟨ht.1.le, lt_trans ht.2 hsL⟩
    have h2 : t / z₂ t ≤ t / z₁ t := div_le_div_of_nonneg_left ht.1.le h1 (hle t ht)
    linarith

/-- On a window [0, s] where z₁ < z₂ inside, E = F₁ − F₂ is strictly monotone. -/
theorem E_smono {L s : ℝ} {z₁ z₂ F₁ F₂ : ℝ → ℝ}
    (hz₁ : ∀ t ∈ Ico 0 L, 0 < z₁ t)
    (cF₁ : ContinuousOn F₁ (Ico 0 L)) (cF₂ : ContinuousOn F₂ (Ico 0 L))
    (dF₁ : ∀ t ∈ Ioo 0 L, HasDerivAt F₁ (t / z₁ t) t)
    (dF₂ : ∀ t ∈ Ioo 0 L, HasDerivAt F₂ (t / z₂ t) t)
    (hsL : s < L) (hlt : ∀ t ∈ Ioo 0 s, z₁ t < z₂ t) :
    StrictMonoOn (fun t => F₁ t - F₂ t) (Icc 0 s) := by
  have hsub : Icc 0 s ⊆ Ico 0 L := fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hsL⟩
  have hsubI : Ioo 0 s ⊆ Ioo 0 L := fun t ht => ⟨ht.1, lt_trans ht.2 hsL⟩
  apply strictMonoOn_of_hasDerivWithinAt_pos (f' := fun t => t / z₁ t - t / z₂ t)
    (convex_Icc 0 s) ((cF₁.mono hsub).sub (cF₂.mono hsub))
  · intro t ht
    rw [interior_Icc] at ht
    exact ((dF₁ t (hsubI ht)).sub (dF₂ t (hsubI ht))).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    have h1 : 0 < z₁ t := hz₁ t ⟨ht.1.le, lt_trans ht.2 hsL⟩
    have h2 : t / z₂ t < t / z₁ t := div_lt_div_of_pos_left ht.1 h1 (hlt t ht)
    linarith

/-- Lemma T (no crossing): two curves of the adverse-pressure Crocco system with equal F at 0 and
z₁(0) < z₂(0) keep z₁ < z₂ on the whole common range (no condition L ≤ 1). -/
theorem no_cross {K L : ℝ} (hK : 0 < K)
    {z₁ z₂ F₁ F₂ : ℝ → ℝ}
    (hz₁ : ∀ t ∈ Ico 0 L, 0 < z₁ t)
    (cz₁ : ContinuousOn z₁ (Ico 0 L)) (cz₂ : ContinuousOn z₂ (Ico 0 L))
    (cF₁ : ContinuousOn F₁ (Ico 0 L)) (cF₂ : ContinuousOn F₂ (Ico 0 L))
    (dF₁ : ∀ t ∈ Ioo 0 L, HasDerivAt F₁ (t / z₁ t) t)
    (dF₂ : ∀ t ∈ Ioo 0 L, HasDerivAt F₂ (t / z₂ t) t)
    (dz₁ : ∀ t ∈ Ioo 0 L, HasDerivAt z₁ (-(K * F₁ t) + (1 - t ^ 2) / z₁ t) t)
    (dz₂ : ∀ t ∈ Ioo 0 L, HasDerivAt z₂ (-(K * F₂ t) + (1 - t ^ 2) / z₂ t) t)
    (hF0 : F₁ 0 = F₂ 0) (hlt : z₁ 0 < z₂ 0) :
    ∀ t ∈ Ico 0 L, z₁ t < z₂ t := by
  intro t₁ ht₁
  by_contra hneg
  rw [not_lt] at hneg
  set D : ℝ → ℝ := fun t => z₂ t - z₁ t with hD
  set S : Set ℝ := Icc 0 t₁ ∩ D ⁻¹' Iic 0 with hS
  have hsub : Icc 0 t₁ ⊆ Ico 0 L := fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 ht₁.2⟩
  have hSc : IsClosed S :=
    ((cz₂.mono hsub).sub (cz₁.mono hsub)).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_Iic
  have hSne : S.Nonempty := ⟨t₁, ⟨ht₁.1, le_refl t₁⟩, show z₂ t₁ - z₁ t₁ ≤ 0 by linarith⟩
  have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  set τ := sInf S with hτdef
  have hτ : τ ∈ S := hSc.csInf_mem hSne hSbdd
  have hDτ : D τ ≤ 0 := hτ.2
  have hτL : τ < L := lt_of_le_of_lt hτ.1.2 ht₁.2
  have hτ0 : 0 < τ := by
    rcases eq_or_lt_of_le hτ.1.1 with h | h
    · exfalso
      rw [← h] at hDτ
      simp only [hD] at hDτ
      linarith
    · exact h
  -- D > 0 on [0, τ)
  have hbefore : ∀ t ∈ Ico 0 τ, 0 < D t := by
    intro t ht
    by_contra hc
    rw [not_lt] at hc
    have htS : t ∈ S := ⟨⟨ht.1, le_trans ht.2.le hτ.1.2⟩, hc⟩
    have := csInf_le hSbdd htS
    linarith [ht.2]
  have hτI : τ ∈ Ioo 0 L := ⟨hτ0, hτL⟩
  have hDcA : ContinuousAt D τ :=
    ((cz₂.sub cz₁) τ ⟨hτ0.le, hτL⟩).continuousAt (Ico_mem_nhds hτ0 hτL)
  -- D τ = 0
  have hDτ0 : D τ = 0 := by
    have hge : 0 ≤ D τ := by
      refine ge_of_tendsto (hDcA.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio τ))) ?_
      filter_upwards [Ioo_mem_nhdsLT hτ0] with y hy
      exact (hbefore y ⟨hy.1.le, hy.2⟩).le
    linarith
  have hzeq : z₁ τ = z₂ τ := by
    simp only [hD] at hDτ0
    linarith
  -- E(τ) > 0
  have hEτ : 0 < F₁ τ - F₂ τ := by
    have hsm := E_smono hz₁ cF₁ cF₂ dF₁ dF₂ hτL (fun t ht => by
      have := hbefore t ⟨ht.1.le, ht.2⟩
      simp only [hD] at this
      linarith)
    have := hsm ⟨le_refl 0, hτ0.le⟩ ⟨hτ0.le, le_refl τ⟩ hτ0
    simp only at this
    rw [hF0] at this
    linarith
  -- D'(τ) = K E(τ) > 0
  have hDd : HasDerivAt D
      ((-(K * F₂ τ) + (1 - τ ^ 2) / z₂ τ) - (-(K * F₁ τ) + (1 - τ ^ 2) / z₁ τ)) τ :=
    (dz₂ τ hτI).sub (dz₁ τ hτI)
  have hdpos : 0 < (-(K * F₂ τ) + (1 - τ ^ 2) / z₂ τ) - (-(K * F₁ τ) + (1 - τ ^ 2) / z₁ τ) := by
    rw [hzeq]
    have : 0 < K * (F₁ τ - F₂ τ) := mul_pos hK hEτ
    linarith
  have hleft := Checked.FalknerSkan.LimitCore.left_neg hDd hdpos hDτ0
  obtain ⟨y, hy1, hy2⟩ := (hleft.and (Ioo_mem_nhdsLT hτ0)).exists
  have := hbefore y ⟨hy2.1.le, hy2.2⟩
  linarith

/-- Lemma T, second part: E = F₁ − F₂ is monotone on [0, L) and positive on (0, L). -/
theorem no_cross_E {K L : ℝ} (hK : 0 < K)
    {z₁ z₂ F₁ F₂ : ℝ → ℝ}
    (hz₁ : ∀ t ∈ Ico 0 L, 0 < z₁ t)
    (cz₁ : ContinuousOn z₁ (Ico 0 L)) (cz₂ : ContinuousOn z₂ (Ico 0 L))
    (cF₁ : ContinuousOn F₁ (Ico 0 L)) (cF₂ : ContinuousOn F₂ (Ico 0 L))
    (dF₁ : ∀ t ∈ Ioo 0 L, HasDerivAt F₁ (t / z₁ t) t)
    (dF₂ : ∀ t ∈ Ioo 0 L, HasDerivAt F₂ (t / z₂ t) t)
    (dz₁ : ∀ t ∈ Ioo 0 L, HasDerivAt z₁ (-(K * F₁ t) + (1 - t ^ 2) / z₁ t) t)
    (dz₂ : ∀ t ∈ Ioo 0 L, HasDerivAt z₂ (-(K * F₂ t) + (1 - t ^ 2) / z₂ t) t)
    (hF0 : F₁ 0 = F₂ 0) (hlt : z₁ 0 < z₂ 0) :
    MonotoneOn (fun t => F₁ t - F₂ t) (Ico 0 L) ∧ ∀ t ∈ Ioo 0 L, F₂ t < F₁ t := by
  have hnc := no_cross hK hz₁ cz₁ cz₂ cF₁ cF₂ dF₁ dF₂ dz₁ dz₂ hF0 hlt
  have hwin : ∀ s, s < L → StrictMonoOn (fun t => F₁ t - F₂ t) (Icc 0 s) := fun s hs =>
    E_smono hz₁ cF₁ cF₂ dF₁ dF₂ hs (fun t ht => hnc t ⟨ht.1.le, lt_trans ht.2 hs⟩)
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    exact (hwin b hb.2).monotoneOn ⟨ha.1, hab⟩ ⟨hb.1, le_refl b⟩ hab
  · intro t ht
    have := hwin t ht.2 ⟨le_refl 0, ht.1.le⟩ ⟨ht.1.le, le_refl t⟩ ht.1
    simp only at this
    rw [hF0] at this
    linarith

end Scratch.NoCross



/-! Scratch (run 2026-11-09T0828Z, fork A): Steps 1 and 2 of Theorem U′ of the β < 0 research
note (`runs/2026-11-09T0428Z/research/fs_negative_beta.md` §2). -/

namespace Scratch.UStep
open Set Filter Topology

/-- Step 1 (Crocco side): with D = z₂ − z₁ ≥ 0 at t₀, E = F₁ − F₂ monotone and G₁' = (1 − s)/z₁,
K E(t₀)(t − t₀) ≤ D(t) + 2(G₁(t) − G₁(t₀)) for t₀ ≤ t < L ≤ 1. -/
theorem step1 {K L t₀ t : ℝ} (hK : 0 ≤ K) (hL : L ≤ 1) (ht₀ : 0 < t₀) (ht : t₀ ≤ t)
    (htL : t < L) {z₁ z₂ F₁ F₂ G₁ : ℝ → ℝ}
    (hz₁ : ∀ s ∈ Ico 0 L, 0 < z₁ s) (hz₂ : ∀ s ∈ Ico 0 L, 0 < z₂ s)
    (cz₁ : ContinuousOn z₁ (Ico 0 L)) (cz₂ : ContinuousOn z₂ (Ico 0 L))
    (cG : ContinuousOn G₁ (Ico 0 L))
    (dz₁ : ∀ s ∈ Ioo 0 L, HasDerivAt z₁ (-(K * F₁ s) + (1 - s ^ 2) / z₁ s) s)
    (dz₂ : ∀ s ∈ Ioo 0 L, HasDerivAt z₂ (-(K * F₂ s) + (1 - s ^ 2) / z₂ s) s)
    (dG : ∀ s ∈ Ioo 0 L, HasDerivAt G₁ ((1 - s) / z₁ s) s)
    (hE : MonotoneOn (fun s => F₁ s - F₂ s) (Ico 0 L)) (hD : z₁ t₀ ≤ z₂ t₀) :
    K * (F₁ t₀ - F₂ t₀) * (t - t₀) ≤ z₂ t - z₁ t + 2 * (G₁ t - G₁ t₀) := by
  have hsub : Icc t₀ t ⊆ Ico 0 L := fun s hs => ⟨ht₀.le.trans hs.1, lt_of_le_of_lt hs.2 htL⟩
  set c := K * (F₁ t₀ - F₂ t₀) with hc
  set Ψ : ℝ → ℝ := fun s => (z₂ s - z₁ s) + 2 * G₁ s - c * s with hΨ
  have hmono : MonotoneOn Ψ (Icc t₀ t) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun s => ((-(K * F₂ s) + (1 - s ^ 2) / z₂ s) - (-(K * F₁ s) + (1 - s ^ 2) / z₁ s))
        + 2 * ((1 - s) / z₁ s) - c)
      (convex_Icc t₀ t)
    · exact (((cz₂.mono hsub).sub (cz₁.mono hsub)).add ((cG.mono hsub).const_smul (2 : ℝ))).sub
        ((continuous_const.mul continuous_id).continuousOn)
    · intro s hs
      rw [interior_Icc] at hs
      have hsI : s ∈ Ioo 0 L := ⟨ht₀.trans hs.1, lt_trans hs.2 htL⟩
      have := (((dz₂ s hsI).sub (dz₁ s hsI)).add ((dG s hsI).const_mul 2)).sub
        ((hasDerivAt_id s).const_mul c)
      refine (this.congr_deriv ?_).hasDerivWithinAt
      simp
    · intro s hs
      rw [interior_Icc] at hs
      have hs0 : 0 < s := ht₀.trans hs.1
      have hsL : s < L := lt_trans hs.2 htL
      have h1 : 0 < z₁ s := hz₁ s ⟨hs0.le, hsL⟩
      have h2 : 0 < z₂ s := hz₂ s ⟨hs0.le, hsL⟩
      have hs1 : s < 1 := lt_of_lt_of_le hsL hL
      have hEs : F₁ t₀ - F₂ t₀ ≤ F₁ s - F₂ s :=
        hE ⟨ht₀.le, lt_of_le_of_lt ht htL⟩ ⟨hs0.le, hsL⟩ hs.1.le
      have hKE : c ≤ K * (F₁ s - F₂ s) := mul_le_mul_of_nonneg_left hEs hK
      -- the pressure and G terms combine to (1 − s)²/z₁ + (1 − s²)/z₂ ≥ 0
      have key : (1 - s ^ 2) / z₂ s - (1 - s ^ 2) / z₁ s + 2 * ((1 - s) / z₁ s)
          = (1 - s) ^ 2 / z₁ s + (1 - s ^ 2) / z₂ s := by
        field_simp
        ring
      have hnn : 0 ≤ (1 - s) ^ 2 / z₁ s + (1 - s ^ 2) / z₂ s := by
        have : 0 ≤ 1 - s ^ 2 := by nlinarith
        positivity
      have : (-(K * F₂ s) + (1 - s ^ 2) / z₂ s - (-(K * F₁ s) + (1 - s ^ 2) / z₁ s))
          + 2 * ((1 - s) / z₁ s) - c
          = (K * (F₁ s - F₂ s) - c) + ((1 - s ^ 2) / z₂ s - (1 - s ^ 2) / z₁ s
            + 2 * ((1 - s) / z₁ s)) := by ring
      rw [this, key]
      linarith
  have h := hmono ⟨le_refl t₀, ht⟩ ⟨ht, le_refl t⟩ ht
  simp only [hΨ] at h
  have : c * (t - t₀) = c * t - c * t₀ := by ring
  rw [this]
  linarith

/-- Step 2 (tail, physical side): if q ≥ M(1 − p) on [η₀, ∞) with M > 0, then
(x − f x) − (η₀ − f η₀) ≤ (p x − p η₀)/M for x ≥ η₀. -/
theorem step2 {f p q : ℝ → ℝ} {M η₀ : ℝ} (hM : 0 < M) (hη₀ : 0 ≤ η₀)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (htail : ∀ η ∈ Ici η₀, M * (1 - p η) ≤ q η) :
    ∀ x ∈ Ici η₀, (x - f x) - (η₀ - f η₀) ≤ (p x - p η₀) / M := by
  intro x hx
  set χ : ℝ → ℝ := fun y => y - f y - p y / M with hχ
  have hχd : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt χ (1 - p η - q η / M) (Ici 0) η := by
    intro η hη
    exact (((hasDerivWithinAt_id η _).sub (hf η hη)).sub ((hp η hη).div_const M))
  have hanti := Checked.FalknerSkan.LimitCore.anti hχd hη₀ (b := x) (fun y hy => by
    have h := htail y hy.1.le
    have : M * (1 - p y) / M ≤ q y / M := div_le_div_of_nonneg_right h hM.le
    rw [mul_div_cancel_left₀ _ hM.ne'] at this
    linarith)
  have h := hanti ⟨le_refl η₀, hx⟩ ⟨hx, le_refl x⟩ hx
  simp only [hχ] at h
  have : (p x - p η₀) / M = p x / M - p η₀ / M := sub_div _ _ _
  rw [this]
  linarith

end Scratch.UStep


/-! Theorem U′ of the β < 0 research note (§2): among BVP solutions with q > 0 on [0, ∞), one
with a Gaussian-type tail (q ≥ M(1 − p) eventually, every M) has the largest wall shear. -/

namespace Scratch.UPrime
open Set Filter Topology
open Checked.FalknerSkan.LimitCore

/-- Hypotheses of one solution of the adverse-pressure system in the monotone class. -/
structure Sol (K : ℝ) (f p q : ℝ → ℝ) : Prop where
  hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η
  hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η
  hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(K * f η * q η) + 1 - p η ^ 2) (Ici 0) η
  hf0 : f 0 = 0
  hp0 : p 0 = 0
  hlim : Tendsto p atTop (𝓝 1)
  hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η

theorem Sol.smono {K : ℝ} {f p q : ℝ → ℝ} (S : Sol K f p q) : StrictMonoOn p (Ici 0) :=
  Checked.FalknerSkan.CroccoWindow.smono_Ici S.hp S.hpos

theorem Sol.bounds {K : ℝ} {f p q : ℝ → ℝ} (S : Sol K f p q) :
    ∀ η ∈ Ici (0 : ℝ), 0 ≤ p η ∧ p η < 1 :=
  Checked.FalknerSkan.BoundedTools.bounded_of_pos S.hp S.hp0 S.hlim S.hpos

/-- Every velocity level s ∈ [0, 1) is reached. -/
theorem Sol.reach {K : ℝ} {f p q : ℝ → ℝ} (S : Sol K f p q) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ∃ u ∈ Ici (0 : ℝ), p u = s := by
  obtain ⟨R, hR⟩ := (S.hlim.eventually (lt_mem_nhds hs1)).exists_forall_of_atTop
  set R' := max R 0
  have hR' : s < p R' := hR R' (le_max_left _ _)
  have hc : ContinuousOn p (Icc 0 R') := cont_of S.hp le_rfl
  obtain ⟨u, hu, hpu⟩ := intermediate_value_Icc (le_max_right R 0) hc
    (show s ∈ Icc (p 0) (p R') by rw [S.hp0]; exact ⟨hs0, hR'.le⟩)
  exact ⟨u, hu.1, hpu⟩

/-- q stays above any ε > 0 on no half-line [T, ∞). -/
theorem Sol.small {K : ℝ} {f p q : ℝ → ℝ} (S : Sol K f p q) {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) :
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

/-- The two Crocco curves on a common range, read at points of equal velocity. -/
theorem pair {K E₁ E₂ : ℝ} (hK : 0 < K) (hE₁ : 0 < E₁) (hE₂ : 0 < E₂)
    {f₁ p₁ q₁ f₂ p₂ q₂ : ℝ → ℝ} (S₁ : Sol K f₁ p₁ q₁) (S₂ : Sol K f₂ p₂ q₂)
    (hlt : q₁ 0 < q₂ 0) :
    (∀ u₁ ∈ Ioo 0 E₁, ∀ u₂ ∈ Ico 0 E₂, p₁ u₁ = p₂ u₂ → f₂ u₂ < f₁ u₁) ∧
    (∀ u₁ ∈ Ico 0 E₁, ∀ u₂ ∈ Ico 0 E₂, ∀ v₁ ∈ Ico 0 E₁, ∀ v₂ ∈ Ico 0 E₂,
      p₁ u₁ = p₂ u₂ → p₁ v₁ = p₂ v₂ → p₁ u₁ ≤ p₁ v₁ → f₁ u₁ - f₂ u₂ ≤ f₁ v₁ - f₂ v₂) ∧
    (∀ u₁ ∈ Ioo 0 E₁, ∀ u₂ ∈ Ico 0 E₂, ∀ v₁ ∈ Ico 0 E₁, ∀ v₂ ∈ Ico 0 E₂,
      p₁ u₁ = p₂ u₂ → p₁ v₁ = p₂ v₂ → p₁ u₁ ≤ p₁ v₁ →
      K * (f₁ u₁ - f₂ u₂) * (p₁ v₁ - p₁ u₁) ≤ q₂ v₂ - q₁ v₁ + 2 * ((v₁ - f₁ v₁) - (u₁ - f₁ u₁))) := by
  have restrict : ∀ {g g' : ℝ → ℝ} {E : ℝ},
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt g (g' η) (Ici 0) η) →
      ∀ η ∈ Icc 0 E, HasDerivWithinAt g (g' η) (Icc 0 E) η := fun hg η hη =>
    (hg η hη.1).mono Icc_subset_Ici_self
  obtain ⟨ψ₁, hψ₁, hψp₁, cz₁, cF₁, dF₁, dz₁, cψ₁, dψ₁⟩ :=
    Scratch.NegCrocco.crocco_pos hE₁ (restrict S₁.hf) (restrict S₁.hp) (restrict S₁.hq) S₁.hp0
      (fun η hη => S₁.hpos η hη.1)
  obtain ⟨ψ₂, hψ₂, hψp₂, cz₂, cF₂, dF₂, dz₂, _, _⟩ :=
    Scratch.NegCrocco.crocco_pos hE₂ (restrict S₂.hf) (restrict S₂.hp) (restrict S₂.hq) S₂.hp0
      (fun η hη => S₂.hpos η hη.1)
  set L := min (p₁ E₁) (p₂ E₂) with hL
  have hL1 : Ico 0 L ⊆ Ico 0 (p₁ E₁) := fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  have hL2 : Ico 0 L ⊆ Ico 0 (p₂ E₂) := fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
  have hI1 : Ioo 0 L ⊆ Ioo 0 (p₁ E₁) := fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  have hI2 : Ioo 0 L ⊆ Ioo 0 (p₂ E₂) := fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
  have hLle : L ≤ 1 := le_trans (min_le_left _ _) (S₁.bounds E₁ hE₁.le).2.le
  have hz₁ : ∀ t ∈ Ico 0 L, 0 < q₁ (ψ₁ t) := fun t ht => S₁.hpos _ (hψ₁ t (hL1 ht)).1.1
  have hz₂ : ∀ t ∈ Ico 0 L, 0 < q₂ (ψ₂ t) := fun t ht => S₂.hpos _ (hψ₂ t (hL2 ht)).1.1
  have hψ0₁ : ψ₁ 0 = 0 := by have := hψp₁ 0 ⟨le_rfl, hE₁⟩; rwa [S₁.hp0] at this
  have hψ0₂ : ψ₂ 0 = 0 := by have := hψp₂ 0 ⟨le_rfl, hE₂⟩; rwa [S₂.hp0] at this
  have hF0 : f₁ (ψ₁ 0) = f₂ (ψ₂ 0) := by rw [hψ0₁, hψ0₂, S₁.hf0, S₂.hf0]
  have hz0 : q₁ (ψ₁ 0) < q₂ (ψ₂ 0) := by rw [hψ0₁, hψ0₂]; exact hlt
  obtain ⟨hEmono, hEpos⟩ := Scratch.NoCross.no_cross_E hK hz₁
    (cz₁.mono hL1) (cz₂.mono hL2) (cF₁.mono hL1) (cF₂.mono hL2)
    (fun t ht => dF₁ t (hI1 ht)) (fun t ht => dF₂ t (hI2 ht))
    (fun t ht => dz₁ t (hI1 ht)) (fun t ht => dz₂ t (hI2 ht)) hF0 hz0
  have hnc := Scratch.NoCross.no_cross hK hz₁
    (cz₁.mono hL1) (cz₂.mono hL2) (cF₁.mono hL1) (cF₂.mono hL2)
    (fun t ht => dF₁ t (hI1 ht)) (fun t ht => dF₂ t (hI2 ht))
    (fun t ht => dz₁ t (hI1 ht)) (fun t ht => dz₂ t (hI2 ht)) hF0 hz0
  -- a point of Ico 0 E₁ has velocity in Ico 0 L when it equals a velocity of the other
  have inL : ∀ u₁ ∈ Ico 0 E₁, ∀ u₂ ∈ Ico 0 E₂, p₁ u₁ = p₂ u₂ → p₁ u₁ ∈ Ico 0 L := by
    intro u₁ hu₁ u₂ hu₂ he
    refine ⟨(S₁.bounds u₁ hu₁.1).1, lt_min ?_ ?_⟩
    · exact S₁.smono hu₁.1 (le_of_lt (lt_of_le_of_lt hu₁.1 hu₁.2)) hu₁.2
    · rw [he]; exact S₂.smono hu₂.1 (le_of_lt (lt_of_le_of_lt hu₂.1 hu₂.2)) hu₂.2
  have back₁ : ∀ u₁ ∈ Ico 0 E₁, ψ₁ (p₁ u₁) = u₁ := hψp₁
  have back₂ : ∀ u₂ ∈ Ico 0 E₂, ψ₂ (p₂ u₂) = u₂ := hψp₂
  refine ⟨?_, ?_, ?_⟩
  · intro u₁ hu₁ u₂ hu₂ he
    have hu₁' : u₁ ∈ Ico 0 E₁ := Ioo_subset_Ico_self hu₁
    have hin := inL u₁ hu₁' u₂ hu₂ he
    have hpos : 0 < p₁ u₁ := by
      have := S₁.smono (mem_Ici.2 le_rfl) hu₁'.1 hu₁.1
      rwa [S₁.hp0] at this
    have := hEpos (p₁ u₁) ⟨hpos, hin.2⟩
    rw [back₁ u₁ hu₁', he, back₂ u₂ hu₂] at this
    exact this
  · intro u₁ hu₁ u₂ hu₂ v₁ hv₁ v₂ hv₂ hu hv huv
    have hinu := inL u₁ hu₁ u₂ hu₂ hu
    have hinv := inL v₁ hv₁ v₂ hv₂ hv
    have := hEmono hinu hinv huv
    simp only at this
    have e2 : ψ₂ (p₁ u₁) = u₂ := by rw [hu]; exact back₂ u₂ hu₂
    have e2v : ψ₂ (p₁ v₁) = v₂ := by rw [hv]; exact back₂ v₂ hv₂
    rw [back₁ u₁ hu₁, back₁ v₁ hv₁, e2, e2v] at this
    exact this
  · intro u₁ hu₁ u₂ hu₂ v₁ hv₁ v₂ hv₂ hu hv huv
    have hu₁' : u₁ ∈ Ico 0 E₁ := Ioo_subset_Ico_self hu₁
    have hinu := inL u₁ hu₁' u₂ hu₂ hu
    have hinv := inL v₁ hv₁ v₂ hv₂ hv
    have hpos : 0 < p₁ u₁ := by
      have := S₁.smono (mem_Ici.2 le_rfl) hu₁'.1 hu₁.1
      rwa [S₁.hp0] at this
    have hG : ∀ s ∈ Ioo 0 L, HasDerivAt (fun t => ψ₁ t - f₁ (ψ₁ t)) ((1 - s) / q₁ (ψ₁ s)) s := by
      intro s hs
      have := (dψ₁ s (hI1 hs)).sub (dF₁ s (hI1 hs))
      refine this.congr_deriv ?_
      have hne := (hz₁ s (Ioo_subset_Ico_self hs)).ne'
      field_simp
    have hcG : ContinuousOn (fun t => ψ₁ t - f₁ (ψ₁ t)) (Ico 0 L) :=
      (cψ₁.mono hL1).sub (cF₁.mono hL1)
    have hD : q₁ (ψ₁ (p₁ u₁)) ≤ q₂ (ψ₂ (p₁ u₁)) := (hnc _ hinu).le
    have h := Scratch.UStep.step1 hK.le hLle hpos huv hinv.2 hz₁ hz₂
      (cz₁.mono hL1) (cz₂.mono hL2) hcG
      (fun t ht => dz₁ t (hI1 ht)) (fun t ht => dz₂ t (hI2 ht)) hG hEmono hD
    have e2 : ψ₂ (p₁ u₁) = u₂ := by rw [hu]; exact back₂ u₂ hu₂
    have e2v : ψ₂ (p₁ v₁) = v₂ := by rw [hv]; exact back₂ v₂ hv₂
    rw [back₁ u₁ hu₁', back₁ v₁ hv₁, e2, e2v] at h
    linarith

/-- Theorem U′: a solution in the monotone class with the Gaussian-type tail has wall shear at
least that of any solution in the monotone class (adverse pressure, any K > 0). -/
theorem u_prime {K : ℝ} (hK : 0 < K)
    {f₁ p₁ q₁ f₂ p₂ q₂ : ℝ → ℝ} (S₁ : Sol K f₁ p₁ q₁) (S₂ : Sol K f₂ p₂ q₂)
    (hexp : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p₁ η) ≤ q₁ η) :
    q₂ 0 ≤ q₁ 0 := by
  by_contra hcon
  push Not at hcon
  -- t* = p₁ 1 and its partner on the second curve
  have hb1 := S₁.bounds 1 (by norm_num)
  have htstar : 0 < p₁ 1 := by
    have := S₁.smono (mem_Ici.2 le_rfl) (show (1 : ℝ) ∈ Ici 0 by norm_num) one_pos
    rwa [S₁.hp0] at this
  obtain ⟨a₂, ha₂, hpa₂⟩ := S₂.reach htstar.le hb1.2
  -- E* > 0
  have hEstar : f₂ a₂ < f₁ 1 :=
    (pair hK (show (0 : ℝ) < 2 by norm_num) (show 0 < a₂ + 1 by linarith [mem_Ici.1 ha₂])
      S₁ S₂ hcon).1 1 ⟨one_pos, by norm_num⟩ a₂ ⟨ha₂, by linarith⟩ hpa₂.symm
  set Es := f₁ 1 - f₂ a₂ with hEs
  have hEs0 : 0 < Es := by linarith
  set M := 4 / (K * Es) with hM
  have hKE : 0 < K * Es := mul_pos hK hEs0
  have hM0 : 0 < M := by positivity
  obtain ⟨N, hN⟩ := (hexp M).exists_forall_of_atTop
  set η₀ := max N 1 with hη₀
  have hη₀1 : 1 ≤ η₀ := le_max_right _ _
  have hη₀0 : 0 ≤ η₀ := by linarith
  have htail : ∀ η ∈ Ici η₀, M * (1 - p₁ η) ≤ q₁ η := fun η hη =>
    hN η (le_trans (le_max_left _ _) hη)
  set t₀ := p₁ η₀ with ht₀
  have hb0 := S₁.bounds η₀ hη₀0
  have ht₀star : p₁ 1 ≤ t₀ :=
    S₁.smono.monotoneOn (show (1 : ℝ) ∈ Ici 0 by norm_num) (mem_Ici.2 hη₀0) hη₀1
  set ε := K * Es * (1 - t₀) / 8 with hε
  have h1t₀ : 0 < 1 - t₀ := by linarith [hb0.2]
  have hε0 : 0 < ε := by rw [hε]; positivity
  -- a point of the second curve beyond velocity (1 + t₀)/2 with small q₂
  obtain ⟨T, hT0, hT⟩ := S₂.reach (s := (1 + t₀) / 2) (by linarith [hb0.1]) (by linarith [hb0.2])
  obtain ⟨η₂, hη₂T, hq₂⟩ := S₂.small hε0 hT0
  have hη₂0 : 0 ≤ η₂ := le_trans hT0 hη₂T
  set t := p₂ η₂ with ht
  have htT : (1 + t₀) / 2 ≤ t := by
    rw [← hT]; exact S₂.smono.monotoneOn hT0 (mem_Ici.2 hη₂0) hη₂T
  have hb2 := S₂.bounds η₂ hη₂0
  obtain ⟨x, hx0, hpx⟩ := S₁.reach (s := t) (by linarith [hb0.1]) hb2.2
  obtain ⟨b₀, hb₀0, hpb₀⟩ := S₂.reach (s := t₀) hb0.1 hb0.2
  have hxη₀ : η₀ ≤ x := by
    by_contra hc
    push Not at hc
    have := S₁.smono (mem_Ici.2 hx0) (mem_Ici.2 hη₀0) hc
    rw [hpx] at this
    linarith [hb0.2]
  have hη₂b : b₀ ≤ η₂ ∧ a₂ ≤ b₀ := by
    constructor
    · by_contra hc
      push Not at hc
      have := S₂.smono (mem_Ici.2 hη₂0) (mem_Ici.2 hb₀0) hc
      rw [hpb₀] at this
      linarith [hb0.2]
    · by_contra hc
      push Not at hc
      have := S₂.smono (mem_Ici.2 hb₀0) ha₂ hc
      rw [hpb₀, hpa₂] at this
      linarith
  -- the final Crocco range
  set E₁ := x + 1
  set E₂ := η₂ + 1
  obtain ⟨_, hmon, hstep⟩ := pair hK (show 0 < E₁ by linarith) (show 0 < E₂ by linarith) S₁ S₂ hcon
  have hmem1 : ∀ y, 0 ≤ y → y ≤ x → y ∈ Ico 0 E₁ := fun y h0 h1 => ⟨h0, by linarith⟩
  have hmem2 : ∀ y, 0 ≤ y → y ≤ η₂ → y ∈ Ico 0 E₂ := fun y h0 h1 => ⟨h0, by linarith⟩
  -- E(t₀) ≥ E*
  have hEt₀ : Es ≤ f₁ η₀ - f₂ b₀ :=
    hmon 1 (hmem1 1 zero_le_one (le_trans hη₀1 hxη₀)) a₂ (hmem2 a₂ ha₂ (le_trans hη₂b.2 hη₂b.1))
      η₀ (hmem1 η₀ hη₀0 hxη₀) b₀ (hmem2 b₀ hb₀0 hη₂b.1) hpa₂.symm (by rw [hpb₀]) ht₀star
  -- Step 1
  have h1 := hstep η₀ ⟨by linarith, by linarith⟩ b₀ (hmem2 b₀ hb₀0 hη₂b.1) x (hmem1 x hx0 le_rfl)
    η₂ (hmem2 η₂ hη₂0 le_rfl) (by rw [hpb₀]) (by rw [hpx]) (by rw [hpx]; linarith)
  -- Step 2
  have h2 := Scratch.UStep.step2 hM0 hη₀0 S₁.hf S₁.hp htail x hxη₀
  rw [hpx] at h1 h2
  have hq₁x : 0 < q₁ x := S₁.hpos x hx0
  -- combine
  have htt : 0 ≤ t - t₀ := by linarith [hb0.2]
  have hA : K * Es * (t - t₀) ≤ K * (f₁ η₀ - f₂ b₀) * (t - t₀) := by
    have := mul_le_mul_of_nonneg_left hEt₀ hK.le
    exact mul_le_mul_of_nonneg_right this htt
  have hB : 2 * ((t - t₀) / M) = K * Es * (t - t₀) / 2 := by
    rw [hM]; field_simp; ring
  have hfin : K * Es * (t - t₀) / 2 ≤ ε := by nlinarith
  have hfin2 : K * Es * (1 - t₀) / 4 ≤ K * Es * (t - t₀) / 2 := by
    have := mul_le_mul_of_nonneg_left (show (1 - t₀) / 2 ≤ t - t₀ by linarith) hKE.le
    linarith
  have : 0 < K * Es * (1 - t₀) := by positivity
  linarith

/-- Theorem U: two solutions of the monotone class with the Gaussian-type tail have the same wall
shear. -/
theorem u_equal_shear {K : ℝ} (hK : 0 < K)
    {f₁ p₁ q₁ f₂ p₂ q₂ : ℝ → ℝ} (S₁ : Sol K f₁ p₁ q₁) (S₂ : Sol K f₂ p₂ q₂)
    (hexp₁ : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p₁ η) ≤ q₁ η)
    (hexp₂ : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p₂ η) ≤ q₂ η) :
    q₁ 0 = q₂ 0 :=
  le_antisymm (u_prime hK S₂ S₁ hexp₂) (u_prime hK S₁ S₂ hexp₁)

end Scratch.UPrime

#print axioms Scratch.UPrime.u_prime
#print axioms Scratch.UPrime.u_equal_shear
