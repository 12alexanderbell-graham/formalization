import Work.Cosmography.B1Separation
import Work.Cosmography.B1SepBlind
import Work.Cosmography.B1DirBlind

/-!
# Audit of `cubic_separation` (run 2026-10-31T0828Z): the blind restatement follows

The blind restater (subagent, did not see `Work/Cosmography/B1Separation.lean`) wrote
`Work.Cosmography.B1SepBlind.blind_separation` from the plain-English claim. Its hypotheses are the
program's with the polynomial evaluated at the literals `3`, `7` and the common offset as an
existential; its conclusion is `5/4 < √(Δa₂² + Δa₃²)`. It follows from the program's statement.
-/

namespace Work.Cosmography.B1SepAudit

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1

theorem blind_closed (Ω : ℝ) (hΩ₁ : 1 / 5 ≤ Ω) (hΩ₂ : Ω ≤ 2 / 5)
    (a : ℝ → ℝ) (t₇ t₃ t₀ : ℝ) (h₇₃ : t₇ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₇ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₇ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₇ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₃ : redshift a t₀ t₃ = 3) (hz₇ : redshift a t₀ t₇ = 7)
    (a₂ a₃ H : ℝ) (hHpos : 0 < H)
    (hP₃ : 0 < logPolyDL3 a₂ a₃ H 3) (hP₇ : 0 < logPolyDL3 a₂ a₃ H 7)
    (hfit : ∃ δ : ℝ,
      |5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL3 a₂ a₃ H 3) - δ| ≤ 1 / 20 ∧
      |5 * Real.logb 10 (lumDistFlat a t₀ t₇ / logPolyDL3 a₂ a₃ H 7) - δ| ≤ 1 / 20) :
    5 / 4 < √((a₂ - lusA2 Ω) ^ 2 + (a₃ - lusA3 Ω) ^ 2) := by
  obtain ⟨c, h3, h7⟩ := hfit
  have h := Work.Cosmography.B1Sep.cubic_separation Ω hΩ₁ hΩ₂ a t₇ t₃ t₀ h₇₃ h₃₀ hpos hdiff hH₀
    hH hz₃ hz₇ a₂ a₃ H c hHpos (by rw [hz₃]; exact hP₃) (by rw [hz₇]; exact hP₇)
    (by rw [hz₃]; exact h3) (by rw [hz₇]; exact h7)
  exact Real.lt_sqrt_of_sq_lt h

/-- The two statements are the same proposition (blind ⇒ program also holds: the blind's
hypotheses are implied by the program's, and `(5/4)² < S ↔ 5/4 < √S`). -/
theorem blind_iff_program_conclusion (S : ℝ) : (5 / 4 : ℝ) ^ 2 < S ↔ 5 / 4 < √S := by
  constructor
  · exact Real.lt_sqrt_of_sq_lt
  · intro h
    have h0 : (0:ℝ) ≤ 5 / 4 := by norm_num
    have := (Real.lt_sqrt h0).1 h
    exact this

end Work.Cosmography.B1SepAudit

namespace Work.Cosmography.B1SepAudit

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1

/-- `5 log₁₀(P/D) = −5 log₁₀(D/P)`. -/
lemma five_logb_swap (P D : ℝ) : 5 * Real.logb 10 (P / D) = -(5 * Real.logb 10 (D / P)) := by
  rw [← inv_div, Real.logb_inv]; ring

/-- Audit of `cubic_direction` (run 0828Z): the blind restatement (`B1DirBlind.blind_direction`,
ratio written polynomial/exact, offset `δ`) follows with offset `c = −δ`. -/
theorem blind_direction_closed (Ω : ℝ) (hΩ₁ : (1 / 5 : ℝ) ≤ Ω) (hΩ₂ : Ω ≤ 2 / 5)
    (a : ℝ → ℝ) (t₇ t₃ t₀ : ℝ) (h₇₃ : t₇ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₇ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₇ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₇ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₃ : redshift a t₀ t₃ = 3) (hz₇ : redshift a t₀ t₇ = 7)
    (a₂ a₃ H : ℝ) (hHpos : 0 < H)
    (hP₃ : 0 < logPolyDL3 a₂ a₃ H 3) (hP₇ : 0 < logPolyDL3 a₂ a₃ H 7)
    (δ : ℝ)
    (hfit₃ : |5 * Real.logb 10 (logPolyDL3 a₂ a₃ H 3 / lumDistFlat a t₀ t₃) - δ| ≤ 5 / 100)
    (hfit₇ : |5 * Real.logb 10 (logPolyDL3 a₂ a₃ H 7 / lumDistFlat a t₀ t₇) - δ| ≤ 5 / 100) :
    a₂ - lusA2 Ω < 7 * Real.logb 10 2 * (a₃ - lusA3 Ω) := by
  rw [five_logb_swap] at hfit₃ hfit₇
  have e : ∀ x : ℝ, |-x - δ| = |x - -δ| := fun x => by rw [← abs_neg]; ring_nf
  rw [e] at hfit₃ hfit₇
  exact Work.Cosmography.B1Sep.cubic_direction Ω hΩ₁ hΩ₂ a t₇ t₃ t₀ h₇₃ h₃₀ hpos hdiff hH₀ hH
    hz₃ hz₇ a₂ a₃ H (-δ) hHpos (by rw [hz₃]; exact hP₃) (by rw [hz₇]; exact hP₇)
    (by rw [hz₃]; linarith [hfit₃]) (by rw [hz₇]; linarith [hfit₇])

end Work.Cosmography.B1SepAudit
