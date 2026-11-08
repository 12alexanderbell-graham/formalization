# Item 41

**Area:** B1 fit level

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `Ω : ℝ`, `a : ℝ → ℝ`, `t₅ : ℝ`, `t₃ : ℝ`, `t₁ : ℝ`, `t₀ : ℝ`, `a₂ : ℝ`, `a₃ : ℝ`, `H : ℝ`, `c : ℝ`:

**assuming**

1. `0 ≤ Ω`
2. `Ω ≤ 1`
3. `t₅ ≤ t₃`
4. `t₃ ≤ t₁`
5. `t₁ ≤ t₀`
6. for every `s : ℝ`, if `s ∈ Set.Icc t₅ t₀`, then `0 < a s`
7. for every `s : ℝ`, if `s ∈ Set.Icc t₅ t₀`, then `DifferentiableAt ℝ a s`
8. `0 < hubble a t₀`
9. for every `s : ℝ`, if `s ∈ Set.Icc t₅ t₀`, then `hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω)`
10. `redshift a t₀ t₁ = √2 - 1`
11. `redshift a t₀ t₃ = 2 * √2 - 1`
12. `redshift a t₀ t₅ = 4 * √2 - 1`
13. `0 < H`
14. `0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₁)`
15. `0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₃)`
16. `0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₅)`
17. `|5 * Real.logb 10 (lumDistFlat a t₀ t₁ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₁)) - c| ≤ 1 / 20`
18. `|5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₃)) - c| ≤ 1 / 20`
19. `|5 * Real.logb 10 (lumDistFlat a t₀ t₅ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₅)) - c| ≤ 1 / 20`

**then**

- `a₂ - lusA2 Ω + 1 / 2 < 20 / 3 * Real.logb 10 2 * (a₃ - lusA3 Ω)`

Program definitions in this claim:

- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): phrase (hand-written, linted): the Hubble rate of the scale factor `a` at time `t`; by definition, `hubble a t` is `deriv a t / a t`
- `logPolyDL3 a₂ a₃ H₀ z` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_logPolyDL3`); its name is not checked (for `a₂ : ℝ`, `a₃ : ℝ`, `H₀ : ℝ`, `z : ℝ`): is defined as `Real.log 10 / H₀ * (Real.logb 10 (1 + z) + a₂ * Real.logb 10 (1 + z) ^ 2 + a₃ * Real.logb 10 (1 + z) ^ 3)`
- `lumDistFlat a t₀ t` — **PINNED** (pin theorem `lumDistFlat_pins`): phrase (hand-written, linted): the spatially flat luminosity distance, at observation time `t₀`, of a source emitting at time `t` (scale factor `a`; units in which the speed of light is one); by definition, `lumDistFlat a t₀ t` is `a t₀ * (1 + redshift a t₀ t) * comoving a t₀ t`
- `lusA2 Ω` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_lusA2`); its name is not checked (for `Ω : ℝ`): is defined as `Real.log 10 * (3 / 2 - 3 / 4 * Ω)`
- `lusA3 Ω` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_lusA3`); its name is not checked (for `Ω : ℝ`): is defined as `Real.log 10 ^ 2 * (9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6)`
- `redshift a t₀ t` — **PINNED** (pin theorem `redshiftCore_pins`): phrase (hand-written, linted): the redshift at observation time `t₀` of light at emission time `t` (scale factor `a`); by definition, `redshift a t₀ t` is `a t₀ / a t - 1`

## Author's paraphrase (hand-written; checked only by prose rules)

**B1 at fit level (direction).** For every `Ω ∈ [0, 1]` and every scale factor obeying
`H = H₀ √(Ω(1+z)³ + 1 − Ω)` (with `H₀ > 0`) on the whole interval back to the farthest source, with
sources at `1 + z = √2, 2√2, 4√2` (`z ≈ 0.41, 1.83, 4.66`), every cubic log-polynomial distance
(coefficients `a₂, a₃`, normalisation `H > 0`, positive at the three redshifts) whose distance
modulus agrees with the exact one (`lumDistFlat`) up to a common offset `c` within 0.05 mag at all
three redshifts satisfies `a₂ − lusA2 Ω + 1/2 < (20/3) log₁₀ 2 · (a₃ − lusA3 Ω)`: it lies beyond a
line through the point `(lusA2 Ω, lusA3 Ω)` of Lusso et al. 2019 Eq. (8), towards smaller `a₂` and
larger `a₃`, by a margin of 1/2 in `a₂`.

## Formal statement (Lean 4)

```lean
theorem fit_direction (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
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
    a₂ - lusA2 Ω + 1 / 2 < 20 / 3 * Real.logb 10 2 * (a₃ - lusA3 Ω) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.BambaY.lumDistFlat`, `Cosmography.hubble`, `Cosmography.redshift`, `Cosmography.B1.logPolyDL3`, `Cosmography.B1.lusA2`, `Cosmography.B1.lusA3`, `Cosmography.BambaY.comoving`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: lumDistFlat, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): logPolyDL3², lusA2², lusA3².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `fit_direction`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): redshift(t₁) = √2 - 1; redshift(t₃) = 2 * √2 - 1; redshift(t₅) = 4 * √2 - 1.
- Source file: `Checked/Cosmography/B1Fit.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 41
