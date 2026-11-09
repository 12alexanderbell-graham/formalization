import Mathlib
import Checked.FalknerSkan.LimitCore

/-! Run 2026-11-09T0828Z (from the scratch file of fork A): Lemma T of the β < 0 research note
(`runs/2026-11-09T0428Z/research/fs_negative_beta.md` §2) — no crossing of two Crocco curves of
the adverse-pressure system z' = −K F + (1 − t²)/z, F' = t/z. -/

namespace Work.FalknerSkan.NegNoCross
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

end Work.FalknerSkan.NegNoCross

/-! Run 2026-11-09T0828Z (from the scratch file of fork A): Steps 1 and 2 of Theorem U′ of the β < 0 research
note (`runs/2026-11-09T0428Z/research/fs_negative_beta.md` §2). -/

namespace Work.FalknerSkan.NegUStep
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

end Work.FalknerSkan.NegUStep
