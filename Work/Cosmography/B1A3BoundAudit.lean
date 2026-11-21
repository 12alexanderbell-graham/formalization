import Work.Cosmography.B1A3Bound
import Work.Cosmography.B1A3BoundBlind

/-!
# Audit of `third_coefficient_lower_bound` (run 2026-11-21T1628Z): the blind restatement follows

The blind restater (Sonnet, brief `runs/2026-11-21T1628Z/blind/BRIEF.md`, did not see the frozen file) wrote
`Work.Cosmography.B1A3BoundBlind.blind_a3_bound` (copied from `runs/2026-11-21T1628Z/blind/` with a namespace added):
the model's present Hubble rate as a separate parameter, the sources strictly ordered in time, the redshifts as
`1 + z`, and the fit condition as one existential offset with `|5 log₁₀ P − 5 log₁₀ d_L − Δ| ≤ 0.05`. It follows from
the frozen statement: the expansion law at the present time identifies the parameter with the present Hubble rate,
and the luminosity distance is positive, so the logarithm of the ratio splits.
-/

namespace Work.Cosmography.B1A3BoundAudit

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1

lemma ld_pos (a : ℝ → ℝ) (t t₀ : ℝ) (htt : t < t₀) (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t t₀, DifferentiableAt ℝ a s) : 0 < lumDistFlat a t₀ t := by
  have hcont : ContinuousOn (fun s => 1 / a s) (Set.Icc t t₀) :=
    ContinuousOn.div continuousOn_const (fun s hs => (hdiff s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hpos s hs).ne')
  have hint : 0 < ∫ s in t..t₀, 1 / a s :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable_of_Icc htt.le)
      (fun s hs => by have := hpos s ⟨hs.1.le, hs.2.le⟩; positivity) htt
  have h0 := hpos t₀ ⟨htt.le, le_rfl⟩
  have h1 := hpos t ⟨le_rfl, htt.le⟩
  have hz : 0 < 1 + redshift a t₀ t := by
    unfold redshift; have : 0 < a t₀ / a t := by positivity
    linarith
  unfold lumDistFlat comoving
  positivity

theorem blind_closed
    (a : ℝ → ℝ) (t₀ t₁ t₂ t₃ : ℝ) (H₀ Ωm : ℝ)
    (hH₀ : 0 < H₀) (hΩ : Ωm ∈ Set.Icc (0 : ℝ) 1)
    (h32 : t₃ < t₂) (h21 : t₂ < t₁) (h10 : t₁ < t₀)
    (hpos : ∀ t ∈ Set.Icc t₃ t₀, 0 < a t)
    (hdiff : ∀ t ∈ Set.Icc t₃ t₀, DifferentiableAt ℝ a t)
    (hlaw : ∀ t ∈ Set.Icc t₃ t₀,
      hubble a t = H₀ * Real.sqrt (Ωm * (1 + redshift a t₀ t) ^ 3 + 1 - Ωm))
    (hz1 : 1 + redshift a t₀ t₁ = Real.sqrt 2)
    (hz2 : 1 + redshift a t₀ t₂ = 2 * Real.sqrt 2)
    (hz3 : 1 + redshift a t₀ t₃ = 4 * Real.sqrt 2)
    (a₂ a₃ H : ℝ) (hH : 0 < H)
    (hp1 : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₁))
    (hp2 : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₂))
    (hp3 : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₃))
    (hfit : ∃ Δ : ℝ,
      |Work.Cosmography.B1A3BoundBlind.blindModulus (logPolyDL3 a₂ a₃ H (redshift a t₀ t₁))
          - Work.Cosmography.B1A3BoundBlind.blindModulus (lumDistFlat a t₀ t₁) - Δ| ≤ 0.05 ∧
      |Work.Cosmography.B1A3BoundBlind.blindModulus (logPolyDL3 a₂ a₃ H (redshift a t₀ t₂))
          - Work.Cosmography.B1A3BoundBlind.blindModulus (lumDistFlat a t₀ t₂) - Δ| ≤ 0.05 ∧
      |Work.Cosmography.B1A3BoundBlind.blindModulus (logPolyDL3 a₂ a₃ H (redshift a t₀ t₃))
          - Work.Cosmography.B1A3BoundBlind.blindModulus (lumDistFlat a t₀ t₃) - Δ| ≤ 0.05) :
    a₃ > 13 / 5 := by
  obtain ⟨Δ, f1, f2, f3⟩ := hfit
  have h30 : t₃ ≤ t₀ := by linarith
  have ha0 : 0 < a t₀ := hpos t₀ ⟨h30, le_rfl⟩
  have hr0 : redshift a t₀ t₀ = 0 := by unfold redshift; rw [div_self ha0.ne']; ring
  have hHt : hubble a t₀ = H₀ := by
    rw [hlaw t₀ ⟨h30, le_rfl⟩, hr0]; norm_num
  have hlaw' : ∀ s ∈ Set.Icc t₃ t₀,
      hubble a s = hubble a t₀ * √(Ωm * (1 + redshift a t₀ s) ^ 3 + 1 - Ωm) := by
    intro s hs; rw [hHt]; exact hlaw s hs
  have sub1 : Set.Icc t₁ t₀ ⊆ Set.Icc t₃ t₀ := Set.Icc_subset_Icc_left (by linarith)
  have sub2 : Set.Icc t₂ t₀ ⊆ Set.Icc t₃ t₀ := Set.Icc_subset_Icc_left (by linarith)
  have d1 := ld_pos a t₁ t₀ h10 (fun s hs => hpos s (sub1 hs)) (fun s hs => hdiff s (sub1 hs))
  have d2 := ld_pos a t₂ t₀ (by linarith) (fun s hs => hpos s (sub2 hs)) (fun s hs => hdiff s (sub2 hs))
  have d3 := ld_pos a t₃ t₀ (by linarith) hpos hdiff
  have key : ∀ d P : ℝ, 0 < d → 0 < P →
      |Work.Cosmography.B1A3BoundBlind.blindModulus P - Work.Cosmography.B1A3BoundBlind.blindModulus d - Δ|
        ≤ 0.05 → |5 * Real.logb 10 (d / P) - (-Δ)| ≤ 1 / 20 := by
    intro d P hd hP h
    unfold Work.Cosmography.B1A3BoundBlind.blindModulus at h
    rw [Real.logb_div hd.ne' hP.ne', abs_sub_comm]
    have e : -Δ - 5 * (Real.logb 10 d - Real.logb 10 P) = 5 * Real.logb 10 P - 5 * Real.logb 10 d - Δ := by
      ring
    rw [e]; norm_num at h ⊢; exact h
  exact Work.Cosmography.B1A3Bound.third_coefficient_lower_bound Ωm hΩ.1 hΩ.2 a t₃ t₂ t₁ t₀
    h32.le h21.le h10.le hpos hdiff (by rw [hHt]; exact hH₀) hlaw' (by linarith) (by linarith)
    (by linarith) a₂ a₃ H (-Δ) hH hp1 hp2 hp3 (key _ _ d1 hp1 f1) (key _ _ d2 hp2 f2) (key _ _ d3 hp3 f3)

end Work.Cosmography.B1A3BoundAudit
