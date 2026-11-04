import Work.Cosmography.B1L19Curved
import Work.Cosmography.B1L19CurvedBlind

/-!
# Audit of `Work.Cosmography.B1L19Curved`: the blind restatement closed in Lean

The blind restater (`Work/Cosmography/B1L19CurvedBlind.lean`, run 2026-11-04T2028Z) chose weaker
hypotheses than the frozen statements: a free `H₀ > 0` instead of `hubble a t₀`, the curvature
relation `K = −Ω_k (H₀ a₀)²` instead of `omega0`, and the Friedmann law only as a one-sided
derivative within `[t₂, t₀]` (no differentiability at the end points, no `hubble`). Both blind
theorems are proved here from the same certificates (`ratio_bound`) through a bridge that needs only
interior derivatives (`comoving_eq_within`).
-/

namespace Work.Cosmography.B1L19CurvedAudit

open Set Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.BambaK
open Checked.Cosmography.Transverse
open Checked.Cosmography.B1 Checked.Cosmography.B1Fit Checked.Cosmography.B1L19
open Work.Cosmography.B1L19CurvedTools Work.Cosmography.B1L19CurvedProof
open Work.Cosmography.B1L19CurvedBlind

/-- `lumDist` through `S`, for any `H₀ > 0` and `K = κ (H₀ a₀)²`, `κ ≥ 0`. -/
lemma lumDist_S (K κ H₀ : ℝ) (a : ℝ → ℝ) (t₀ t J : ℝ) (ha₀ : 0 < a t₀) (hH₀ : 0 < H₀)
    (hκ : 0 ≤ κ) (hK : K = κ * (H₀ * a t₀) ^ 2) (hχ : comoving a t₀ t = J / (H₀ * a t₀)) :
    lumDist K a t₀ t = (1 + redshift a t₀ t) / H₀ * S κ J := by
  unfold lumDist transverse S
  rw [hχ, hK]
  rcases eq_or_lt_of_le hκ with h0 | h0
  · subst h0; simp; field_simp
  · have hp : 0 < κ * (H₀ * a t₀) ^ 2 := by positivity
    have hne : κ ≠ 0 := h0.ne'
    simp only [hp, ite_true, hne, ite_false]
    have hs : √(κ * (H₀ * a t₀) ^ 2) = √κ * (H₀ * a t₀) := by
      rw [Real.sqrt_mul hκ, Real.sqrt_sq (by positivity)]
    rw [hs]
    have harg : √κ * (H₀ * a t₀) * (J / (H₀ * a t₀)) = √κ * J := by field_simp
    rw [harg]
    have : 0 < √κ := Real.sqrt_pos.2 h0
    field_simp

lemma sqrt_algB (m k a₀ as W : ℝ) (hW : 0 < W) (ha₀ : 0 < a₀) (has : as = W ^ 2 * a₀)
    (hin : 0 < yC m k W) :
    √(m * (a₀ / as) ^ 3 + k * (a₀ / as) ^ 2 + (1 - m - k)) = √(yC m k W) / W ^ 3 := by
  have := sqrt_algC m k a₀ as W hW ha₀ has hin
  rw [← this]; congr 1; ring

/-- Bridge with one-sided derivatives within `[t₂, t₀]` and a free `H₀`. -/
theorem comoving_eq_within {m k : ℝ} (hd : Dom m k) (H₀ : ℝ) (hH₀ : 0 < H₀)
    (a : ℝ → ℝ) (t₂ t t₀ : ℝ) (h2t : t₂ ≤ t) (htt : t ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₂ t₀, 0 < a s)
    (hder : ∀ s ∈ Set.Icc t₂ t₀,
      HasDerivWithinAt a (a s * H₀ * lcdmE m k (a t₀ / a s)) (Set.Icc t₂ t₀) s) :
    comoving a t₀ t = (∫ v in √(a t / a t₀)..1, gC m k v) / (H₀ * a t₀) := by
  set a₀ := a t₀ with ha₀def
  have ha₀ : 0 < a₀ := hpos t₀ ⟨le_trans h2t htt, le_rfl⟩
  have hsub : Icc t t₀ ⊆ Icc t₂ t₀ := Icc_subset_Icc_left h2t
  have hcont : ContinuousOn a (Icc t t₀) := fun s hs => ((hder s (hsub hs)).continuousWithinAt).mono hsub
  set G : ℝ → ℝ := fun x => ∫ v in (1:ℝ)..x, gC m k v with hGdef
  have hG : ∀ x, 0 < x → HasDerivAt G (gC m k x) x := by
    intro x hx
    have hsub' : uIcc (1:ℝ) x ⊆ Ioi 0 := by
      intro y hy; rcases mem_uIcc.1 hy with h | h
      · exact lt_of_lt_of_le one_pos h.1
      · exact lt_of_lt_of_le hx h.1
    exact intervalIntegral.integral_hasDerivAt_right (((gC_cont hd).mono hsub').intervalIntegrable)
      ((gC_cont hd).stronglyMeasurableAtFilter isOpen_Ioi x hx)
      ((gC_cont hd).continuousAt (Ioi_mem_nhds hx))
  set W : ℝ → ℝ := fun s => √(a s / a₀) with hWdef
  set F : ℝ → ℝ := fun s => G (W s) / (H₀ * a₀) with hFdef
  have hWpos : ∀ s ∈ Icc t t₀, 0 < W s := fun s hs =>
    Real.sqrt_pos.2 (div_pos (hpos s (hsub hs)) ha₀)
  have hFc : ContinuousOn F (Icc t t₀) := by
    intro s hs
    have hW : ContinuousWithinAt W (Icc t t₀) s :=
      ((hcont s hs).div_const a₀).sqrt
    have hGc : ContinuousAt G (W s) := (hG (W s) (hWpos s hs)).continuousAt
    exact (hGc.comp_continuousWithinAt hW).div_const _
  have hF : ∀ s ∈ Ioo t t₀, HasDerivWithinAt F (1 / a s) (Ioi s) s := by
    intro s hs
    have hsI : s ∈ Icc t₂ t₀ := ⟨le_trans h2t hs.1.le, hs.2.le⟩
    have hda : HasDerivAt a (a s * H₀ * lcdmE m k (a t₀ / a s)) s :=
      (hder s hsI).hasDerivAt (Icc_mem_nhds (lt_of_le_of_lt h2t hs.1) hs.2)
    apply HasDerivAt.hasDerivWithinAt
    have has := hpos s hsI
    have hr : 0 < a s / a₀ := div_pos has ha₀
    have hWs : 0 < W s := Real.sqrt_pos.2 hr
    have hW2 : a s = W s ^ 2 * a₀ := by
      simp only [hWdef]; rw [Real.sq_sqrt hr.le]; field_simp
    have hd' : HasDerivAt W ((a s * H₀ * lcdmE m k (a t₀ / a s) / a₀) / (2 * √(a s / a₀))) s :=
      (hda.div_const a₀).sqrt hr.ne'
    have hc := ((hG (W s) hWs).comp s hd').div_const (H₀ * a₀)
    have hin := yC_pos hd (W s) hWs
    have hE : lcdmE m k (a t₀ / a s) = √(yC m k (W s)) / W s ^ 3 := by
      unfold lcdmE; rw [← ha₀def]; exact sqrt_algB m k a₀ (a s) (W s) hWs ha₀ hW2 hin
    rw [hE] at hc
    have := deriv_alg H₀ a₀ (a s) (a s * H₀ * (√(yC m k (W s)) / W s ^ 3)) _ (W s) hWs
      (Real.sqrt_pos.2 hin) ha₀ hH₀ hW2 rfl
    exact hc.congr_deriv (by simpa [gC] using this)
  have hint : IntervalIntegrable (fun s => 1 / a s) MeasureTheory.volume t t₀ := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le htt]
    exact continuousOn_const.div hcont (fun x hx => (hpos x (hsub hx)).ne')
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le htt hFc hF hint
  have hW0 : W t₀ = 1 := by
    show √(a t₀ / a₀) = 1
    rw [← ha₀def, div_self ha₀.ne', Real.sqrt_one]
  have hG1 : G 1 = 0 := by simp [hGdef]
  unfold comoving
  rw [hftc]
  simp only [hFdef, hW0, hG1]
  rw [intervalIntegral.integral_symm]
  simp only [hGdef, hWdef]
  ring

/-- The blind `snQso_residual_gap` follows from the certificates (blind restatement closed). -/
theorem blind_sq_closed (H₀ Ωm Ωk K : ℝ) (a : ℝ → ℝ) (t₀ t₁ t₂ : ℝ)
    (h : Setup H₀ Ωm Ωk K a t₀ t₁ t₂) (Hfit : ℝ) (hHfit : 0 < Hfit) :
    residual K a t₀ t₂ 3.075 4.466 (-3.716) Hfit
      - residual K a t₀ t₁ 3.075 4.466 (-3.716) Hfit > 1 / 4 := by
  obtain ⟨hH₀, hm0, hm1, hk0, hk1, hK, ⟨h20, hpos, hder⟩, ht1, hz1, hz2⟩ := h
  have hd : Dom Ωm Ωk := ⟨hm0, hm1, hk0, hk1⟩
  have ha₀ : 0 < a t₀ := hpos t₀ ⟨h20, le_rfl⟩
  have ha1 : 0 < a t₁ := hpos t₁ ht1
  have ha2 : 0 < a t₂ := hpos t₂ ⟨le_rfl, h20⟩
  have hχ1 := comoving_eq_within hd H₀ hH₀ a t₂ t₁ t₀ ht1.1 ht1.2 hpos hder
  have hχ2 := comoving_eq_within hd H₀ hH₀ a t₂ t₂ t₀ le_rfl h20 hpos hder
  have hK' : K = (-Ωk) * (H₀ * a t₀) ^ 2 := by rw [hK]
  have hd1 := lumDist_S K (-Ωk) H₀ a t₀ t₁ _ ha₀ hH₀ (by linarith) hK' hχ1
  have hd2 := lumDist_S K (-Ωk) H₀ a t₀ t₂ _ ha₀ hH₀ (by linarith) hK' hχ2
  obtain ⟨hL1, hL2⟩ := L_bounds
  obtain ⟨hQ5, hF⟩ := poly_sq _ hL1 hL2
  have hQ3 : 0 < 3 / 2 * (Real.log 2 / Real.log 10) + 3.075 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + 4.466 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + (-3.716) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4 := by linarith
  have hδ := delta_core Ωm Ωk (-Ωk) hd rfl K H₀ hH₀ a t₂ t₁ t₀ ha₀ ha1 ha2 hd1 hd2 hz1 hz2
    3.075 4.466 (-3.716) Hfit hHfit _ _ x3_eq x5_eq hQ3 hQ5
  have hq : (1.1225 : ℝ) < 27 / 10 * (3 / 2 * (Real.log 2 / Real.log 10)
      + 3.075 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + 4.466 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + (-3.716) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4)
      / (5 / 2 * (Real.log 2 / Real.log 10) + 3.075 * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + 4.466 * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + (-3.716) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 4) := by
    rw [lt_div_iff₀ hQ5]; linarith
  have hlg := Real.logb_lt_logb (by norm_num : (1:ℝ) < 10) (by norm_num) hq
  have := logb_11225
  unfold Work.Cosmography.B1L19CurvedBlind.residual
  linarith

/-- The blind `snQsoGrb_residual_gap` follows from the certificates (blind restatement closed). -/
theorem blind_sqg_closed (H₀ Ωm Ωk K : ℝ) (a : ℝ → ℝ) (t₀ t₁ t₂ : ℝ)
    (h : Setup H₀ Ωm Ωk K a t₀ t₁ t₂) (Hfit : ℝ) (hHfit : 0 < Hfit) :
    residual K a t₀ t₂ 3.205 3.564 (-2.510) Hfit
      - residual K a t₀ t₁ 3.205 3.564 (-2.510) Hfit > 3 / 20 := by
  obtain ⟨hH₀, hm0, hm1, hk0, hk1, hK, ⟨h20, hpos, hder⟩, ht1, hz1, hz2⟩ := h
  have hd : Dom Ωm Ωk := ⟨hm0, hm1, hk0, hk1⟩
  have ha₀ : 0 < a t₀ := hpos t₀ ⟨h20, le_rfl⟩
  have ha1 : 0 < a t₁ := hpos t₁ ht1
  have ha2 : 0 < a t₂ := hpos t₂ ⟨le_rfl, h20⟩
  have hχ1 := comoving_eq_within hd H₀ hH₀ a t₂ t₁ t₀ ht1.1 ht1.2 hpos hder
  have hχ2 := comoving_eq_within hd H₀ hH₀ a t₂ t₂ t₀ le_rfl h20 hpos hder
  have hK' : K = (-Ωk) * (H₀ * a t₀) ^ 2 := by rw [hK]
  have hd1 := lumDist_S K (-Ωk) H₀ a t₀ t₁ _ ha₀ hH₀ (by linarith) hK' hχ1
  have hd2 := lumDist_S K (-Ωk) H₀ a t₀ t₂ _ ha₀ hH₀ (by linarith) hK' hχ2
  obtain ⟨hL1, hL2⟩ := L_bounds
  obtain ⟨hQ5, hF⟩ := poly_sqg _ hL1 hL2
  have hQ3 : 0 < 3 / 2 * (Real.log 2 / Real.log 10) + 3.205 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + 3.564 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + (-2.510) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4 := by linarith
  have hδ := delta_core Ωm Ωk (-Ωk) hd rfl K H₀ hH₀ a t₂ t₁ t₀ ha₀ ha1 ha2 hd1 hd2 hz1 hz2
    3.205 3.564 (-2.510) Hfit hHfit _ _ x3_eq x5_eq hQ3 hQ5
  have hq : (1.08 : ℝ) < 27 / 10 * (3 / 2 * (Real.log 2 / Real.log 10)
      + 3.205 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + 3.564 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + (-2.510) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4)
      / (5 / 2 * (Real.log 2 / Real.log 10) + 3.205 * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + 3.564 * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + (-2.510) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 4) := by
    rw [lt_div_iff₀ hQ5]; linarith
  have hlg := Real.logb_lt_logb (by norm_num : (1:ℝ) < 10) (by norm_num) hq
  have := logb_108
  unfold Work.Cosmography.B1L19CurvedBlind.residual
  linarith

/-- The blind theorems are literally the frozen-audit statements (closure of the blind file). -/
theorem blind_closed :
    (∀ (H₀ Ωm Ωk K : ℝ) (a : ℝ → ℝ) (t₀ t₁ t₂ : ℝ), Setup H₀ Ωm Ωk K a t₀ t₁ t₂ → ∀ Hfit : ℝ,
      0 < Hfit → residual K a t₀ t₂ 3.075 4.466 (-3.716) Hfit
        - residual K a t₀ t₁ 3.075 4.466 (-3.716) Hfit > 1 / 4) ∧
    (∀ (H₀ Ωm Ωk K : ℝ) (a : ℝ → ℝ) (t₀ t₁ t₂ : ℝ), Setup H₀ Ωm Ωk K a t₀ t₁ t₂ → ∀ Hfit : ℝ,
      0 < Hfit → residual K a t₀ t₂ 3.205 3.564 (-2.510) Hfit
        - residual K a t₀ t₁ 3.205 3.564 (-2.510) Hfit > 3 / 20) :=
  ⟨fun H₀ Ωm Ωk K a t₀ t₁ t₂ h Hfit hH => blind_sq_closed H₀ Ωm Ωk K a t₀ t₁ t₂ h Hfit hH,
   fun H₀ Ωm Ωk K a t₀ t₁ t₂ h Hfit hH => blind_sqg_closed H₀ Ωm Ωk K a t₀ t₁ t₂ h Hfit hH⟩

#print axioms blind_closed
#print axioms Work.Cosmography.B1L19Curved.l19_sq_curved
#print axioms Work.Cosmography.B1L19Curved.l19_sqg_curved

end Work.Cosmography.B1L19CurvedAudit
