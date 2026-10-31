import Checked.Cosmography.B1Truncation

/-!
# B1 separation: a cubic log-polynomial that reproduces exact ΛCDM cannot sit at the ΛCDM point

**Question (TARGETS.md, B1; STATE "B1 separation theorem").** Risaliti & Lusso 2019 (Nat. Astron.
3, 272; arXiv:1811.02590) and Lusso et al. 2019 (A&A 628, L4; arXiv:1907.07692) fit the Hubble
diagram with `D_L = ln(10)(c/H₀)(x + a₂x² + a₃x³)`, `x = log₁₀(1+z)`, and report a > 4σ distance
of the fitted `(a₂, a₃)` from the point flat ΛCDM implies (`lusA2 Ω`, `lusA3 Ω`, Lusso et al. 2019
Eq. (8)). If the universe is exactly flat ΛCDM, where does a cubic that *reproduces* it land?

**Statement.** For every flat ΛCDM model with `Ω ∈ [0.2, 0.4]` (same hypotheses as
`Checked.Cosmography.B1.cubic_shape_miss`: the Friedmann law holds on the whole interval back to a
source at `z = 7`), and every cubic log-polynomial — any coefficients `a₂, a₃`, any normalisation
`H > 0`, any magnitude offset `c` — whose distance modulus agrees with the exact one up to the
common offset `c` within 0.05 mag at both `z = 3` and `z = 7`:
`(a₂ − a₂^ΛCDM)² + (a₃ − a₃^ΛCDM)² > (5/4)²`.
In words: matching exact ΛCDM to 0.05 mag at z = 3 and z = 7 forces the fitted coefficients more
than 1.25 (Euclidean, in the papers' (a₂, a₃) units) away from the ΛCDM-implied point.

Positivity of the polynomial distance at both redshifts is assumed (a negative distance has no
distance modulus; `Real.logb` would silently take the absolute value).

Conventions: as `Checked.Cosmography.B1` (`c = 1`, `hubble a t = ȧ/a`,
`redshift a t₀ t = a(t₀)/a(t) − 1`, `lumDistFlat`; distance-modulus difference `5 log₁₀(d/d')`).

FROZEN (annex 40.1) in run 2026-10-31T0828Z before proof work.
-/

namespace Work.Cosmography.B1Sep

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1

/-- **B1 separation.** In every flat ΛCDM model with `Ω ∈ [0.2, 0.4]` (sources at `z = 3`, `z = 7`),
any cubic log-polynomial (coefficients `a₂, a₃`, normalisation `H > 0`, positive at both
redshifts) that reproduces the exact distance modulus up to a common offset `c` within 0.05 mag
at `z = 3` and at `z = 7` has `(a₂, a₃)` at Euclidean distance more than `5/4` from the
ΛCDM-implied point `(lusA2 Ω, lusA3 Ω)`. -/
theorem cubic_separation (Ω : ℝ) (hΩ₁ : 1 / 5 ≤ Ω) (hΩ₂ : Ω ≤ 2 / 5)
    (a : ℝ → ℝ) (t₇ t₃ t₀ : ℝ) (h₇₃ : t₇ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₇ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₇ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₇ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₃ : redshift a t₀ t₃ = 3) (hz₇ : redshift a t₀ t₇ = 7)
    (a₂ a₃ H c : ℝ) (hHp : 0 < H)
    (hp₃ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₃))
    (hp₇ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₇))
    (hm₃ : |5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₃)) - c|
      ≤ 1 / 20)
    (hm₇ : |5 * Real.logb 10 (lumDistFlat a t₀ t₇ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₇)) - c|
      ≤ 1 / 20) :
    (5 / 4) ^ 2 < (a₂ - lusA2 Ω) ^ 2 + (a₃ - lusA3 Ω) ^ 2 := by
  sorry

end Work.Cosmography.B1Sep
