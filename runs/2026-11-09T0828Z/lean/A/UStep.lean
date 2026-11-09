import Checked.FalknerSkan.LimitCore
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

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

#print axioms Scratch.UStep.step1
#print axioms Scratch.UStep.step2
