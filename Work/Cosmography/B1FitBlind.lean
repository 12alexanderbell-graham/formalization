import Checked.Cosmography.B1Truncation

/-!
# B1 (blind restatement): a 0.05-mag cubic fit to exact flat ΛCDM lies beyond a line

Blind restatement written from the claim in words only (no access to the program's own
statement). Proof deliberately `sorry`.

**Claim in words.** If the universe is exactly flat ΛCDM with matter density `Ω ∈ [0, 1]`
(Friedmann law `H = H₀ √(Ω(1+z)³ + 1 − Ω)`), then every cubic log-polynomial
`D_L = ln(10)/H · (x + a₂x² + a₃x³)`, `x = log₁₀(1+z)`, with any `a₂, a₃`, any `H > 0` and any
magnitude zero-point offset, whose distance modulus agrees with the exact flat-ΛCDM distance
modulus up to that common offset within 0.05 mag at `1 + z = √2, 2√2, 4√2` (and which is
positive there) satisfies `a₂ − a₂^ΛCDM + 1/2 < (20/3) log₁₀ 2 · (a₃ − a₃^ΛCDM)`.

## Hypothesis choices and resolution of ambiguities

1. **The model.** A scale factor `a : ℝ → ℝ`, an observation time `t₀`, the model's true Hubble
   constant `H₀ > 0` and `Ω ∈ [0, 1]` (closed interval: "between 0 and 1 inclusive").
   Units `c = 1`, as in the program's `logPolyDL3` and `lumDistFlat`.

2. **Sources at the stated redshifts.** Three emission times `t₁ t₂ t₃` with
   `1 + redshift a t₀ tᵢ = √2, 2√2, 4√2` respectively (`redshift a t₀ t = a(t₀)/a(t) − 1`).
   The ordering `t₃ ≤ t₂, t₁ ≤ t₀` is imposed directly (membership in `[t₃, t₀]`), so that the
   single interval `[t₃, t₀]` contains every light path; it would otherwise follow from
   monotonicity of `a`, but stating it avoids a hidden appeal to that.

3. **Where the Friedmann law holds.** On the whole closed interval `[t₃, t₀]` from the earliest
   (highest-redshift) emission to observation: at every `s` there, `a s > 0`, `a` is
   differentiable at `s` (two-sided, also at the endpoints — a mild strengthening a physicist
   accepts for a smooth scale factor), and
   `hubble a s = H₀ * √(Ω (1 + redshift a t₀ s)³ + 1 − Ω)`. The law is *not* required outside
   `[t₃, t₀]`, nor only in a neighbourhood of `t₀` (a local law would not determine `d_L`
   at finite redshift). At `s = t₀` it gives `H(t₀) = H₀`, so `H₀` really is the model's
   present Hubble rate.

4. **Exact distance.** `Checked.Cosmography.BambaY.lumDistFlat a t₀ tᵢ`
   (`= a(t₀)(1+z)∫_{tᵢ}^{t₀} dt'/a`), i.e. the luminosity distance computed from the scale
   factor itself, not from a closed-form integral in `z` — the theorem must hold for *any*
   `a` obeying the law, which is the content of "the universe is exactly flat ΛCDM".

5. **What happens to `H₀` (normalisation).** The cubic carries its own normalisation `H > 0`,
   quantified independently of the model's `H₀`; nothing ties them. (Together with the
   offset `δ` this is redundant — both shift `μ` by a constant — but the claim says "any
   normalisation H > 0, any … offset", so both are kept.)

6. **"Distance modulus agrees up to a common offset within 0.05 mag."** Distance modulus
   `μ(d) = 5 log₁₀ d + const`; the additive constant (25 for Mpc) cancels in differences, so
   it is dropped. One real offset `δ` (any sign), *common* to the three redshifts, and for
   each redshift `|5 log₁₀ D_poly − 5 log₁₀ d_L − δ| ≤ 0.05`. I read "within 0.05 mag" as
   non-strict `≤` (the weaker hypothesis, hence the stronger theorem). `δ` is universally
   quantified (it is "any offset" for which the agreement holds), which is equivalent to
   "there exists an offset making the agreement hold" with the existential in hypothesis
   position.

7. **Positivity.** `0 < logPolyDL3 a₂ a₃ H z` at the three redshifts, as the claim demands
   (otherwise `log₁₀` of a nonpositive number is Lean's junk value). The exact `d_L` is
   positive automatically under the hypotheses, so no positivity hypothesis is added for it.

8. **The polynomial is evaluated at the numeric redshifts** `z = √2 − 1, 2√2 − 1, 4√2 − 1`
   (equal to `redshift a t₀ tᵢ` by hypothesis 2), so that `x = log₁₀(1+z) = ½, 3/2, 5/2 ·
   log₁₀ 2`.

9. **ΛCDM-implied point.** `(lusA2 Ω, lusA3 Ω)` = Lusso et al. 2019 Eq. (8) with the `ln 10`
   powers, as given. The same `Ω` as the model's.

10. **"The far side of the line" vs. the displayed inequality.** The words say "the line
    through the ΛCDM-implied point with slope (20/3) log₁₀ 2 in the (a₃, a₂)-plane" (a₃
    horizontal, a₂ vertical), but the displayed inequality carries a `+1/2`, i.e. it is the
    strict half-plane below the *parallel line shifted down by 1/2 in a₂*:
    `a₂ − a₂^ΛCDM < (20/3) log₁₀ 2 (a₃ − a₃^ΛCDM) − 1/2`. I formalise the displayed inequality
    exactly (it is the stronger and more specific reading; in particular it excludes the
    ΛCDM point itself by a margin). "Far side" is taken to mean the side given by that
    inequality (larger `a₃` / smaller `a₂`).
-/

namespace Work.Cosmography.B1FitBlind

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1

/-- Blind restatement of the B1 fit-region claim (see module docstring for every choice). -/
theorem cubic_fit_beyond_line
    -- the flat ΛCDM model
    (a : ℝ → ℝ) (t₀ H₀ Ω : ℝ) (hH₀ : 0 < H₀) (hΩ : Ω ∈ Set.Icc (0 : ℝ) 1)
    -- three sources, earliest emission t₃
    (t₁ t₂ t₃ : ℝ) (ht₁ : t₁ ∈ Set.Icc t₃ t₀) (ht₂ : t₂ ∈ Set.Icc t₃ t₀) (ht₃ : t₃ ≤ t₀)
    (hz₁ : 1 + redshift a t₀ t₁ = √2)
    (hz₂ : 1 + redshift a t₀ t₂ = 2 * √2)
    (hz₃ : 1 + redshift a t₀ t₃ = 4 * √2)
    -- Friedmann law on the whole interval [t₃, t₀]
    (hFried : ∀ s ∈ Set.Icc t₃ t₀, 0 < a s ∧ DifferentiableAt ℝ a s ∧
      hubble a s = H₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    -- the cubic: any coefficients, any normalisation, any common zero-point offset
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
  sorry

end Work.Cosmography.B1FitBlind
