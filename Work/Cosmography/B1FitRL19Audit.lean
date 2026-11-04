import Work.Cosmography.B1FitRL19
import Work.Cosmography.B1FitRL19Blind
import Work.Cosmography.B1FitAudit

/-!
# Audit of `rl19_box_unmatched` (run 2026-11-04T0228Z): the blind restatement follows

The blind restater (subagent, did not see `Work/Cosmography/B1FitRL19.lean`) wrote
`Work.Cosmography.B1FitRL19Blind.rl19_box_cannot_fit_flatLCDM`: model's `H₀` as a parameter, an
interval `[T, t₀]` containing the three sources in any order, the fit as `¬ ∃ a₂ a₃ H δ, …` with
`|5 log₁₀ P − 5 log₁₀ d_L − δ| ≤ 0.05`, box with decimal endpoints. It follows from the program's
general form `fit_direction_gen` and the box lemma `box_neg`.
-/

namespace Work.Cosmography.B1FitRL19Audit

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1
  Work.Cosmography.B1Fit Work.Cosmography.B1FitAudit

theorem blind_closed
    (a : ℝ → ℝ) (Ω H₀ T t₀ t₁ t₂ t₃ : ℝ)
    (hΩ : Ω ∈ Set.Icc (0 : ℝ) 1) (hH₀ : 0 < H₀) (hT : T < t₀)
    (ha_pos : ∀ t ∈ Set.Icc T t₀, 0 < a t)
    (ha_diff : ∀ t ∈ Set.Icc T t₀, DifferentiableAt ℝ a t)
    (hFried : ∀ t ∈ Set.Icc T t₀,
      hubble a t = H₀ * Real.sqrt (Ω * (1 + redshift a t₀ t) ^ 3 + 1 - Ω))
    (ht₁ : t₁ ∈ Set.Icc T t₀) (ht₂ : t₂ ∈ Set.Icc T t₀) (ht₃ : t₃ ∈ Set.Icc T t₀)
    (hz₁ : redshift a t₀ t₁ = Real.sqrt 2 - 1)
    (hz₂ : redshift a t₀ t₂ = 2 * Real.sqrt 2 - 1)
    (hz₃ : redshift a t₀ t₃ = 4 * Real.sqrt 2 - 1) :
    ¬ ∃ a₂ a₃ H δ : ℝ,
      a₂ ∈ Set.Icc (3.43 : ℝ) 3.49 ∧ a₃ ∈ Set.Icc (1.57 : ℝ) 1.69 ∧ 0 < H ∧
      0 < logPolyDL3 a₂ a₃ H (Real.sqrt 2 - 1) ∧
      0 < logPolyDL3 a₂ a₃ H (2 * Real.sqrt 2 - 1) ∧
      0 < logPolyDL3 a₂ a₃ H (4 * Real.sqrt 2 - 1) ∧
      |5 * Real.logb 10 (logPolyDL3 a₂ a₃ H (Real.sqrt 2 - 1))
          - 5 * Real.logb 10 (lumDistFlat a t₀ t₁) - δ| ≤ 0.05 ∧
      |5 * Real.logb 10 (logPolyDL3 a₂ a₃ H (2 * Real.sqrt 2 - 1))
          - 5 * Real.logb 10 (lumDistFlat a t₀ t₂) - δ| ≤ 0.05 ∧
      |5 * Real.logb 10 (logPolyDL3 a₂ a₃ H (4 * Real.sqrt 2 - 1))
          - 5 * Real.logb 10 (lumDistFlat a t₀ t₃) - δ| ≤ 0.05 := by
  rintro ⟨a₂, a₃, H, δ, h2, h3, hH, p1, p2, p3, f1, f2, f3⟩
  obtain ⟨h0, h1⟩ := hΩ
  have ht₀ : t₀ ∈ Set.Icc T t₀ := ⟨hT.le, le_rfl⟩
  have hz0 : redshift a t₀ t₀ = 0 := by
    unfold redshift; rw [div_self (ha_pos t₀ ht₀).ne']; ring
  have hHt : hubble a t₀ = H₀ := by
    rw [hFried t₀ ht₀, hz0]; norm_num
  have hHlaw : ∀ s ∈ Set.Icc T t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω) := by
    intro s hs; rw [hHt]; exact hFried s hs
  have hHt0 : 0 < hubble a t₀ := by rw [hHt]; exact hH₀
  have hq2 : (1:ℝ) < √2 := by
    rw [show (1:ℝ) = √1 from Real.sqrt_one.symm]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have sub : ∀ t ∈ Set.Icc T t₀, Set.Icc t t₀ ⊆ Set.Icc T t₀ :=
    fun t ht => Set.Icc_subset_Icc_left ht.1
  have hd1 := dist_pos Ω h0 h1 a t₁ t₀ (√2) ht₁.2 (fun s hs => ha_pos s (sub t₁ ht₁ hs))
    (fun s hs => ha_diff s (sub t₁ ht₁ hs)) hHt0 (fun s hs => hHlaw s (sub t₁ ht₁ hs))
    (by linarith) hq2
  have hd2 := dist_pos Ω h0 h1 a t₂ t₀ (2 * √2) ht₂.2 (fun s hs => ha_pos s (sub t₂ ht₂ hs))
    (fun s hs => ha_diff s (sub t₂ ht₂ hs)) hHt0 (fun s hs => hHlaw s (sub t₂ ht₂ hs))
    (by linarith) (by linarith)
  have hd3 := dist_pos Ω h0 h1 a t₃ t₀ (4 * √2) ht₃.2 (fun s hs => ha_pos s (sub t₃ ht₃ hs))
    (fun s hs => ha_diff s (sub t₃ ht₃ hs)) hHt0 (fun s hs => hHlaw s (sub t₃ ht₃ hs))
    (by linarith) (by linarith)
  have hf := fit_direction_gen Ω h0 h1 a T t₃ t₂ t₁ t₀ ht₁ ht₂ ht₃ ha_pos ha_diff hHt0 hHlaw
    hz₁ hz₂ hz₃ a₂ a₃ H (-δ) hH (by rw [hz₁]; exact p1) (by rw [hz₂]; exact p2)
    (by rw [hz₃]; exact p3) (by rw [hz₁]; exact fit_conv _ _ δ hd1 p1 f1)
    (by rw [hz₂]; exact fit_conv _ _ δ hd2 p2 f2) (by rw [hz₃]; exact fit_conv _ _ δ hd3 p3 f3)
  obtain ⟨hL1, hL2⟩ := Work.Cosmography.B1FitWitness.t_bounds
  have hl1 := log_ten_ge
  have hl2 := Work.Cosmography.B1FitWitness.log_ten_le
  have hneg := Work.Cosmography.B1FitRL19.box_neg Ω a₂ a₃ (Real.log 10) (Real.logb 10 2) h0 h1
    ⟨by norm_num at h2 ⊢; linarith [h2.1], by norm_num at h2 ⊢; linarith [h2.2]⟩
    ⟨by norm_num at h3 ⊢; linarith [h3.1], by norm_num at h3 ⊢; linarith [h3.2]⟩
    (by norm_num at hl1 ⊢; linarith) (by norm_num at hl2 ⊢; linarith) hL1 hL2
  unfold lusA2 lusA3 at hf
  nlinarith

/-- The closed statement is exactly the blind one (same proposition, checked by the kernel). -/
example : Work.Cosmography.B1FitRL19Blind.rl19_box_cannot_fit_flatLCDM = blind_closed := rfl

end Work.Cosmography.B1FitRL19Audit
