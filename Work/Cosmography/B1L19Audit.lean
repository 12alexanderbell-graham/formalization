import Work.Cosmography.B1L19
import Work.Cosmography.B1L19Blind

/-!
# Audit of the B1 fourth-order theorems: the blind restatement closed in Lean

The blind restater (`Work/Cosmography/B1L19Blind.lean`, written without seeing
`Work/Cosmography/B1L19.lean`) chose a weaker set of hypotheses than the frozen statements:
no differentiability of the scale factor, no order between the two emission times, a free
normalisation `k > 0` besides `H > 0`, the closed coordinate box of the printed ±1σ ranges, and no
positivity hypothesis on the fitted distance. Each blind claim is derived here from the frozen
theorem: differentiability follows from `hubble ≠ 0` (a non-differentiable point has derivative 0),
the order of the emission times from the strict monotonicity of `a` (positive derivative on the
epoch), positivity of the quartic from the box, and `k` is absorbed into `H`.
-/

namespace Work.Cosmography.B1L19Audit

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1
open Work.Cosmography.B1L19 Work.Cosmography.B1L19Blind

lemma radicand_pos (Ω w : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1) (hw : 0 < w) :
    0 < Ω * w ^ 3 + 1 - Ω := by
  rcases lt_or_eq_of_le hΩ₁ with h | h
  · have : 0 ≤ Ω * w ^ 3 := mul_nonneg hΩ₀ (by positivity)
    linarith
  · subst h; have : 0 < w ^ 3 := by positivity
    linarith

/-- The blind hypotheses give the frozen ones, with the emission times in order. -/
lemma reduce (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1) (a : ℝ → ℝ) (t₂ t₄ t₀ : ℝ)
    (h₂ : t₂ ≤ t₀) (h₄ : t₄ ≤ t₀) (hΛ : FlatLCDMOn Ω a (min t₂ t₄) t₀)
    (hz₂ : redshift a t₀ t₂ = 2 * √2 - 1) (hz₄ : redshift a t₀ t₄ = 4 * √2 - 1) :
    t₄ ≤ t₂ ∧ (∀ s ∈ Set.Icc t₄ t₀, 0 < a s) ∧ (∀ s ∈ Set.Icc t₄ t₀, DifferentiableAt ℝ a s) ∧
      0 < hubble a t₀ ∧ (∀ s ∈ Set.Icc t₄ t₀,
        hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω)) := by
  obtain ⟨hH₀, hs⟩ := hΛ
  set m := min t₂ t₄ with hm
  have hm₀ : m ≤ t₀ := le_trans (min_le_left _ _) h₂
  have ha₀ : 0 < a t₀ := (hs t₀ ⟨hm₀, le_rfl⟩).1
  -- the derivative is positive on the epoch
  have hder : ∀ s ∈ Set.Icc m t₀, 0 < deriv a s := by
    intro s hsI
    obtain ⟨has, hhs⟩ := hs s hsI
    have hz : 0 < 1 + redshift a t₀ s := by
      unfold redshift; have : 0 < a t₀ / a s := div_pos ha₀ has; linarith
    have hsq : 0 < √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω) :=
      Real.sqrt_pos.2 (radicand_pos Ω _ hΩ₀ hΩ₁ hz)
    have hhp : 0 < hubble a s := by rw [hhs]; exact mul_pos hH₀ hsq
    unfold hubble at hhp
    exact (div_pos_iff_of_pos_right has).1 hhp
  have hdiffm : ∀ s ∈ Set.Icc m t₀, DifferentiableAt ℝ a s := by
    intro s hsI
    by_contra hnd
    have := hder s hsI
    rw [deriv_zero_of_not_differentiableAt hnd] at this
    exact lt_irrefl _ this
  -- order of the emission times
  have hord : t₄ ≤ t₂ := by
    by_contra hlt
    rw [not_le] at hlt
    have hmt : m = t₂ := min_eq_left hlt.le
    have hmono : StrictMonoOn a (Set.Icc m t₀) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc m t₀)
      · intro s hsI; exact (hdiffm s hsI).continuousAt.continuousWithinAt
      · intro s hsI; rw [interior_Icc] at hsI; exact hder s ⟨hsI.1.le, hsI.2.le⟩
    have hlt' : a t₂ < a t₄ := hmono ⟨by rw [hmt], h₂⟩ ⟨by rw [hmt]; exact hlt.le, h₄⟩ hlt
    have ha₂ : 0 < a t₂ := (hs t₂ ⟨min_le_left _ _, h₂⟩).1
    have ha₄ : 0 < a t₄ := (hs t₄ ⟨min_le_right _ _, h₄⟩).1
    unfold redshift at hz₂ hz₄
    have hq : 0 < √2 := by positivity
    have e : a t₀ / a t₂ < a t₀ / a t₄ := by linarith
    rw [div_lt_div_iff₀ ha₂ ha₄] at e
    have := mul_lt_mul_of_pos_left hlt' ha₀
    linarith
  have hmt : m = t₄ := min_eq_right hord
  refine ⟨hord, fun s hsI => (hs s (by rw [hmt]; exact hsI)).1,
    fun s hsI => hdiffm s (by rw [hmt]; exact hsI), hH₀,
    fun s hsI => (hs s (by rw [hmt]; exact hsI)).2⟩

lemma quartic_eq (k a₂ a₃ a₄ H z : ℝ) (hk : 0 < k) :
    quarticDL k a₂ a₃ a₄ H z = logPolyDL4 a₂ a₃ a₄ (H / k) z := by
  unfold quarticDL logPolyDL4
  field_simp

/-- Positivity of the quartic at the farther source on a box with these lower ends. -/
lemma quartic_pos5 (a₂ a₃ a₄ H : ℝ) (hH : 0 < H) (b₂ b₃ b₄ : ℝ) (ha₂ : b₂ ≤ a₂) (ha₃ : b₃ ≤ a₃)
    (ha₄ : b₄ ≤ a₄) (hb : 0 < 76 / 100 + b₂ * (75 / 100) ^ 2 + b₃ * (75 / 100) ^ 3
      + b₄ * (76 / 100) ^ 4 - 1 / 100) (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃) (hb₄ : b₄ ≤ 0) :
    0 < logPolyDL4 a₂ a₃ a₄ H (4 * √2 - 1) := by
  unfold logPolyDL4
  rw [x5_eq]
  obtain ⟨hL1, hL2⟩ := L_bounds
  set L := Real.log 2 / Real.log 10
  set x := 5 / 2 * L with hx
  have hx1 : 75 / 100 ≤ x := by rw [hx]; linarith
  have hx2 : x ≤ 76 / 100 := by rw [hx]; linarith
  have hx0 : 0 ≤ x := by linarith
  have h2 : b₂ * (75 / 100) ^ 2 ≤ a₂ * x ^ 2 := by
    have : ((75:ℝ) / 100) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) hx1 2
    nlinarith [mul_le_mul this ha₂ hb₂ (by positivity)]
  have h3 : b₃ * (75 / 100) ^ 3 ≤ a₃ * x ^ 3 := by
    have : ((75:ℝ) / 100) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx1 3
    nlinarith [mul_le_mul this ha₃ hb₃ (by positivity)]
  have h4 : b₄ * (76 / 100) ^ 4 ≤ a₄ * x ^ 4 := by
    have hx4 : x ^ 4 ≤ ((76:ℝ) / 100) ^ 4 := pow_le_pow_left₀ hx0 hx2 4
    have hx40 : 0 ≤ x ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right ha₄ hx40, mul_le_mul_of_nonpos_left hx4 hb₄]
  have hl : 0 < Real.log 10 := Real.log_pos (by norm_num)
  apply mul_pos (div_pos hl hH)
  linarith

theorem blind_sq_central_closed (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₂ t₄ t₀ : ℝ) (h₂ : t₂ ≤ t₀) (h₄ : t₄ ≤ t₀)
    (hΛ : FlatLCDMOn Ω a (min t₂ t₄) t₀)
    (hz₂ : redshift a t₀ t₂ = 2 * √2 - 1) (hz₄ : redshift a t₀ t₄ = 4 * √2 - 1)
    (k H : ℝ) (hk : 0 < k) (hH : 0 < H) :
    (35 / 100 : ℝ) <
      resid (lumDistFlat a t₀ t₄) (quarticDL k 3.075 4.466 (-3.716) H (redshift a t₀ t₄)) -
      resid (lumDistFlat a t₀ t₂) (quarticDL k 3.075 4.466 (-3.716) H (redshift a t₀ t₂)) := by
  obtain ⟨hord, hpos, hdiff, hH₀, hHl⟩ := reduce Ω hΩ₀ hΩ₁ a t₂ t₄ t₀ h₂ h₄ hΛ hz₂ hz₄
  have := l19_sq_central Ω hΩ₀ hΩ₁ a t₄ t₂ t₀ hord h₂ hpos hdiff hH₀ hHl hz₂ hz₄ (H / k)
    (div_pos hH hk)
  unfold resid
  rw [quartic_eq _ _ _ _ _ _ hk, quartic_eq _ _ _ _ _ _ hk]
  norm_num at this ⊢
  linarith

theorem blind_sqg_central_closed (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₂ t₄ t₀ : ℝ) (h₂ : t₂ ≤ t₀) (h₄ : t₄ ≤ t₀)
    (hΛ : FlatLCDMOn Ω a (min t₂ t₄) t₀)
    (hz₂ : redshift a t₀ t₂ = 2 * √2 - 1) (hz₄ : redshift a t₀ t₄ = 4 * √2 - 1)
    (k H : ℝ) (hk : 0 < k) (hH : 0 < H) :
    (3 / 10 : ℝ) <
      resid (lumDistFlat a t₀ t₄) (quarticDL k 3.205 3.564 (-2.510) H (redshift a t₀ t₄)) -
      resid (lumDistFlat a t₀ t₂) (quarticDL k 3.205 3.564 (-2.510) H (redshift a t₀ t₂)) := by
  obtain ⟨hord, hpos, hdiff, hH₀, hHl⟩ := reduce Ω hΩ₀ hΩ₁ a t₂ t₄ t₀ h₂ h₄ hΛ hz₂ hz₄
  have := l19_sqg_central Ω hΩ₀ hΩ₁ a t₄ t₂ t₀ hord h₂ hpos hdiff hH₀ hHl hz₂ hz₄ (H / k)
    (div_pos hH hk)
  unfold resid
  rw [quartic_eq _ _ _ _ _ _ hk, quartic_eq _ _ _ _ _ _ hk]
  linarith

theorem blind_sq_box_closed (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₂ t₄ t₀ : ℝ) (h₂ : t₂ ≤ t₀) (h₄ : t₄ ≤ t₀)
    (hΛ : FlatLCDMOn Ω a (min t₂ t₄) t₀)
    (hz₂ : redshift a t₀ t₂ = 2 * √2 - 1) (hz₄ : redshift a t₀ t₄ = 4 * √2 - 1)
    (a₂ a₃ a₄ : ℝ)
    (ha₂ : a₂ ∈ Set.Icc (3.075 - 0.169) (3.075 + 0.172))
    (ha₃ : a₃ ∈ Set.Icc (4.466 - 1.040) (4.466 + 1.013))
    (ha₄ : a₄ ∈ Set.Icc (-3.716 - 1.852) (-3.716 + 1.922))
    (k H : ℝ) (hk : 0 < k) (hH : 0 < H) :
    resid (lumDistFlat a t₀ t₂) (quarticDL k a₂ a₃ a₄ H (redshift a t₀ t₂)) <
      resid (lumDistFlat a t₀ t₄) (quarticDL k a₂ a₃ a₄ H (redshift a t₀ t₄)) := by
  obtain ⟨hord, hpos, hdiff, hH₀, hHl⟩ := reduce Ω hΩ₀ hΩ₁ a t₂ t₄ t₀ h₂ h₄ hΛ hz₂ hz₄
  have hHk : 0 < H / k := div_pos hH hk
  have hp₅ : 0 < logPolyDL4 a₂ a₃ a₄ (H / k) (redshift a t₀ t₄) := by
    rw [hz₄]
    exact quartic_pos5 a₂ a₃ a₄ _ hHk (3.075 - 0.169) (4.466 - 1.040) (-3.716 - 1.852)
      ha₂.1 ha₃.1 ha₄.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have := l19_sq_box Ω hΩ₀ hΩ₁ a t₄ t₂ t₀ hord h₂ hpos hdiff hH₀ hHl hz₂ hz₄ a₂ a₃ a₄ (H / k)
    hHk (le_trans (by norm_num) ha₂.1) (le_trans ha₃.2 (by norm_num))
    (le_trans ha₄.2 (by norm_num)) hp₅
  unfold resid
  rw [quartic_eq _ _ _ _ _ _ hk, quartic_eq _ _ _ _ _ _ hk]
  exact this

theorem blind_sqg_box_closed (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₂ t₄ t₀ : ℝ) (h₂ : t₂ ≤ t₀) (h₄ : t₄ ≤ t₀)
    (hΛ : FlatLCDMOn Ω a (min t₂ t₄) t₀)
    (hz₂ : redshift a t₀ t₂ = 2 * √2 - 1) (hz₄ : redshift a t₀ t₄ = 4 * √2 - 1)
    (a₂ a₃ a₄ : ℝ)
    (ha₂ : a₂ ∈ Set.Icc (3.205 - 0.162) (3.205 + 0.165))
    (ha₃ : a₃ ∈ Set.Icc (3.564 - 0.938) (3.564 + 0.916))
    (ha₄ : a₄ ∈ Set.Icc (-2.510 - 1.536) (-2.510 + 1.595))
    (k H : ℝ) (hk : 0 < k) (hH : 0 < H) :
    resid (lumDistFlat a t₀ t₂) (quarticDL k a₂ a₃ a₄ H (redshift a t₀ t₂)) <
      resid (lumDistFlat a t₀ t₄) (quarticDL k a₂ a₃ a₄ H (redshift a t₀ t₄)) := by
  obtain ⟨hord, hpos, hdiff, hH₀, hHl⟩ := reduce Ω hΩ₀ hΩ₁ a t₂ t₄ t₀ h₂ h₄ hΛ hz₂ hz₄
  have hHk : 0 < H / k := div_pos hH hk
  have hp₅ : 0 < logPolyDL4 a₂ a₃ a₄ (H / k) (redshift a t₀ t₄) := by
    rw [hz₄]
    exact quartic_pos5 a₂ a₃ a₄ _ hHk (3.205 - 0.162) (3.564 - 0.938) (-2.510 - 1.536)
      ha₂.1 ha₃.1 ha₄.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have := l19_sqg_box Ω hΩ₀ hΩ₁ a t₄ t₂ t₀ hord h₂ hpos hdiff hH₀ hHl hz₂ hz₄ a₂ a₃ a₄ (H / k)
    hHk (le_trans (by norm_num) ha₂.1) (le_trans ha₃.2 (by norm_num))
    (le_trans ha₄.2 (by norm_num)) hp₅
  unfold resid
  rw [quartic_eq _ _ _ _ _ _ hk, quartic_eq _ _ _ _ _ _ hk]
  exact this

end Work.Cosmography.B1L19Audit
