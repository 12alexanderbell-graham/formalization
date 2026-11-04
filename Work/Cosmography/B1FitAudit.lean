import Work.Cosmography.B1Fit
import Work.Cosmography.B1FitBlind

/-!
# Audit of `fit_direction` (run 2026-11-04T0228Z): the blind restatement follows

The blind restater (subagent, did not see `Work/Cosmography/B1Fit.lean`) wrote
`Work.Cosmography.B1FitBlind.cubic_fit_beyond_line` from the claim in words. Differences from
the program's statement: the model's `H₀` is a separate parameter (`hubble a t₀ = H₀` follows
from the law at `s = t₀`); sources are only required to lie in `[t₃, t₀]` (no order between the
two nearer ones); the fit condition is written `|5 log₁₀ P − 5 log₁₀ d_L − δ| ≤ 0.05`; the
polynomial is evaluated at the literal redshifts. Its conclusion is identical. It follows from
the program's general form `fit_direction_gen`.
-/

namespace Work.Cosmography.B1FitAudit

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1
  Work.Cosmography.B1Fit

lemma dist_pos (Ω : ℝ) (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1) (a : ℝ → ℝ) (t t₀ s : ℝ) (htt : t ≤ t₀)
    (hpos : ∀ x ∈ Set.Icc t t₀, 0 < a x) (hdiff : ∀ x ∈ Set.Icc t t₀, DifferentiableAt ℝ a x)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ x ∈ Set.Icc t t₀,
      hubble a x = hubble a t₀ * √(Ω * (1 + redshift a t₀ x) ^ 3 + 1 - Ω))
    (hz : 1 + redshift a t₀ t = s) (hs : 1 < s) : 0 < lumDistFlat a t₀ t := by
  have hbr := lumDistFlat_flatLCDM Ω h0 h1 a t t₀ htt hpos hdiff hH₀ hH
  have hz' : redshift a t₀ t = s - 1 := by linarith
  rw [ratio_of_z a t t₀ _ (hpos t ⟨le_rfl, htt⟩) (hpos t₀ ⟨htt, le_rfl⟩) hz',
    show 1 + (s - 1) = s by ring, hz] at hbr
  obtain ⟨hw0, hw1⟩ := w_lt_one s hs
  have hJ := Jpos Ω _ h0 h1 hw0 hw1
  unfold gL at hJ
  rw [hbr]; exact mul_pos (div_pos (by linarith) hH₀) hJ

lemma fit_conv (d P δ : ℝ) (hd : 0 < d) (hP : 0 < P)
    (h : |5 * Real.logb 10 P - 5 * Real.logb 10 d - δ| ≤ 0.05) :
    |5 * Real.logb 10 (d / P) - -δ| ≤ 1 / 20 := by
  rw [Real.logb_div hd.ne' hP.ne']
  have e : 5 * (Real.logb 10 d - Real.logb 10 P) - -δ
      = -(5 * Real.logb 10 P - 5 * Real.logb 10 d - δ) := by ring
  rw [e, abs_neg]; norm_num at h ⊢; exact h

theorem blind_closed (a : ℝ → ℝ) (t₀ H₀ Ω : ℝ) (hH₀ : 0 < H₀) (hΩ : Ω ∈ Set.Icc (0 : ℝ) 1)
    (t₁ t₂ t₃ : ℝ) (ht₁ : t₁ ∈ Set.Icc t₃ t₀) (ht₂ : t₂ ∈ Set.Icc t₃ t₀) (ht₃ : t₃ ≤ t₀)
    (hz₁ : 1 + redshift a t₀ t₁ = √2)
    (hz₂ : 1 + redshift a t₀ t₂ = 2 * √2)
    (hz₃ : 1 + redshift a t₀ t₃ = 4 * √2)
    (hFried : ∀ s ∈ Set.Icc t₃ t₀, 0 < a s ∧ DifferentiableAt ℝ a s ∧
      hubble a s = H₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (a₂ a₃ H δ : ℝ) (hH : 0 < H)
    (hpos₁ : 0 < logPolyDL3 a₂ a₃ H (√2 - 1))
    (hpos₂ : 0 < logPolyDL3 a₂ a₃ H (2 * √2 - 1))
    (hpos₃ : 0 < logPolyDL3 a₂ a₃ H (4 * √2 - 1))
    (hfit₁ : |5 * Real.logb 10 (logPolyDL3 a₂ a₃ H (√2 - 1))
        - 5 * Real.logb 10 (lumDistFlat a t₀ t₁) - δ| ≤ 0.05)
    (hfit₂ : |5 * Real.logb 10 (logPolyDL3 a₂ a₃ H (2 * √2 - 1))
        - 5 * Real.logb 10 (lumDistFlat a t₀ t₂) - δ| ≤ 0.05)
    (hfit₃ : |5 * Real.logb 10 (logPolyDL3 a₂ a₃ H (4 * √2 - 1))
        - 5 * Real.logb 10 (lumDistFlat a t₀ t₃) - δ| ≤ 0.05) :
    a₂ - lusA2 Ω + 1 / 2 < 20 / 3 * Real.logb 10 2 * (a₃ - lusA3 Ω) := by
  obtain ⟨h0, h1⟩ := hΩ
  have hpos : ∀ s ∈ Set.Icc t₃ t₀, 0 < a s := fun s hs => (hFried s hs).1
  have hdiff : ∀ s ∈ Set.Icc t₃ t₀, DifferentiableAt ℝ a s := fun s hs => (hFried s hs).2.1
  have hz0 : redshift a t₀ t₀ = 0 := by
    unfold redshift; rw [div_self (hpos t₀ ⟨ht₃, le_rfl⟩).ne']; ring
  have hHt : hubble a t₀ = H₀ := by
    rw [(hFried t₀ ⟨ht₃, le_rfl⟩).2.2, hz0]; norm_num
  have hHlaw : ∀ s ∈ Set.Icc t₃ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω) := by
    intro s hs; rw [hHt]; exact (hFried s hs).2.2
  have hHt0 : 0 < hubble a t₀ := by rw [hHt]; exact hH₀
  have hq2 : (1:ℝ) < √2 := by
    rw [show (1:ℝ) = √1 from Real.sqrt_one.symm]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hz₁' : redshift a t₀ t₁ = √2 - 1 := by linarith
  have hz₂' : redshift a t₀ t₂ = 2 * √2 - 1 := by linarith
  have hz₃' : redshift a t₀ t₃ = 4 * √2 - 1 := by linarith
  have sub1 : Set.Icc t₁ t₀ ⊆ Set.Icc t₃ t₀ := Set.Icc_subset_Icc_left ht₁.1
  have sub2 : Set.Icc t₂ t₀ ⊆ Set.Icc t₃ t₀ := Set.Icc_subset_Icc_left ht₂.1
  have hd1 := dist_pos Ω h0 h1 a t₁ t₀ _ ht₁.2 (fun s hs => hpos s (sub1 hs))
    (fun s hs => hdiff s (sub1 hs)) hHt0 (fun s hs => hHlaw s (sub1 hs)) hz₁ hq2
  have hd2 := dist_pos Ω h0 h1 a t₂ t₀ _ ht₂.2 (fun s hs => hpos s (sub2 hs))
    (fun s hs => hdiff s (sub2 hs)) hHt0 (fun s hs => hHlaw s (sub2 hs)) hz₂ (by linarith)
  have hd3 := dist_pos Ω h0 h1 a t₃ t₀ _ ht₃ hpos hdiff hHt0 hHlaw hz₃ (by linarith)
  refine fit_direction_gen Ω h0 h1 a t₃ t₂ t₁ t₀ ht₁ ht₂ ht₃ hpos hdiff hHt0 hHlaw hz₁' hz₂' hz₃'
    a₂ a₃ H (-δ) hH ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hz₁']; exact hpos₁
  · rw [hz₂']; exact hpos₂
  · rw [hz₃']; exact hpos₃
  · rw [hz₁']; exact fit_conv _ _ δ hd1 hpos₁ hfit₁
  · rw [hz₂']; exact fit_conv _ _ δ hd2 hpos₂ hfit₂
  · rw [hz₃']; exact fit_conv _ _ δ hd3 hpos₃ hfit₃

/-- The closed statement is exactly the blind one (same proposition, checked by the kernel). -/
example : Work.Cosmography.B1FitBlind.cubic_fit_beyond_line = blind_closed := rfl

end Work.Cosmography.B1FitAudit
