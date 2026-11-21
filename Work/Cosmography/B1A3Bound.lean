import Checked.Cosmography.B1FitRL19
import Checked.Cosmography.B1A3Tools

/-! B1 at fit level, `B1A3Bound`: a lower bound on the third coefficient of every cubic log-polynomial that matches an
exact flat ΛCDM distance modulus over the quasar range (FROZEN by run 2026-11-21T1628Z before its proof).

The hypotheses are those of `Checked.Cosmography.B1FitRL19.rl19_box_unmatched` with the box removed: a density in the
unit interval, the three sources at one plus redshift equal to the square root of two, twice and four times it, and
a distance modulus within a twentieth of a magnitude of the exact one, up to a common offset, at all three. The
conclusion bounds the third coefficient from below by thirteen fifths, whatever the second coefficient; a float scan
(`runs/2026-11-21T1628Z/scripts/scan_a3_onesided.py`, unchecked) puts the smallest third coefficient of a matching
cubic near two and sixty-four hundredths, at density one. The route is the proof of
`Checked.Trust.NecessityBN.bn_a3_large` with new cell certificates. -/

namespace Work.Cosmography.B1A3Bound
open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1

/-- For every density `Ω` with `0 ≤ Ω` and `Ω ≤ 1`, if the scale factor `a` has Hubble rate
`hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω)` between the emission time `t₅` and the
observation time `t₀` and the log-polynomial luminosity distance `logPolyDL3 a₂ a₃ H` (with `0 < H`) is positive at
the three redshifts `√2 - 1`, `2 * √2 - 1`, `4 * √2 - 1` and has `5 * Real.logb 10` of the ratio of the flat
luminosity distance to it within `1 / 20` of one value `c` at the three redshifts, then its third coefficient
satisfies `13 / 5 < a₃`, for every second coefficient `a₂`. -/
theorem third_coefficient_lower_bound (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₅ t₃ t₁ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₁ : t₃ ≤ t₁) (h₁₀ : t₁ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₁ : redshift a t₀ t₁ = √2 - 1) (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1)
    (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)
    (a₂ a₃ H c : ℝ) (hHp : 0 < H)
    (hp₁ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₁))
    (hp₃ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₃))
    (hp₅ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₅))
    (hm₁ : |5 * Real.logb 10 (lumDistFlat a t₀ t₁ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₁)) - c|
      ≤ 1 / 20)
    (hm₃ : |5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₃)) - c|
      ≤ 1 / 20)
    (hm₅ : |5 * Real.logb 10 (lumDistFlat a t₀ t₅ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₅)) - c|
      ≤ 1 / 20) :
    13 / 5 < a₃ :=
  Checked.Cosmography.B1A3Tools.a3_bound_gen Ω hΩ₀ hΩ₁ a t₅ t₅ t₃ t₁ t₀ ⟨le_trans h₅₃ h₃₁, h₁₀⟩
    ⟨h₅₃, le_trans h₃₁ h₁₀⟩ ⟨le_rfl, le_trans h₅₃ (le_trans h₃₁ h₁₀)⟩ hpos hdiff hH₀ hH hz₁ hz₃ hz₅
    a₂ a₃ H c hHp hp₁ hp₃ hp₅ hm₁ hm₃ hm₅

end Work.Cosmography.B1A3Bound
