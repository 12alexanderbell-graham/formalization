# Item 31

**Area:** B1

**Source:** Risaliti & Lusso, Nat. Astron. 3, 272 (2019); Lusso et al., A&A 628, L4 (2019), Eq. (8): third-order log-polynomial distance and its ΛCDM-implied coefficients

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `Ω : ℝ`, `a : ℝ → ℝ`, `t₇ : ℝ`, `t₃ : ℝ`, `t₀ : ℝ`:

**assuming**

1. `1 / 5 ≤ Ω`
2. `Ω ≤ 2 / 5`
3. `t₇ ≤ t₃`
4. `t₃ ≤ t₀`
5. for every `s : ℝ`, if `s ∈ Set.Icc t₇ t₀`, then `0 < a s`
6. for every `s : ℝ`, if `s ∈ Set.Icc t₇ t₀`, then `DifferentiableAt ℝ a s`
7. `0 < hubble a t₀`
8. for every `s : ℝ`, if `s ∈ Set.Icc t₇ t₀`, then `hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω)`
9. `redshift a t₀ t₃ = 3`
10. `redshift a t₀ t₇ = 7`

**then**

- `18 / 100 < 5 * Real.logb 10 (lumDistFlat a t₀ t₇ / logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t₇)) - 5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t₃))`

Program definitions in this claim:

- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): the Hubble rate a′(t)/a(t) of the scale factor `a` at time `t`
- `logPolyDL3 a₂ a₃ H₀ z` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_logPolyDL3`); its name is not checked (for `a₂ : ℝ`, `a₃ : ℝ`, `H₀ : ℝ`, `z : ℝ`): is defined as `Real.log 10 / H₀ * (Real.logb 10 (1 + z) + a₂ * Real.logb 10 (1 + z) ^ 2 + a₃ * Real.logb 10 (1 + z) ^ 3)`
- `lumDistFlat a t₀ t` — **PINNED** (pin theorem `lumDistFlat_pins`): the spatially flat luminosity distance a(t₀)·(1 + z)·χ, at observation time `t₀`, of a source emitting at time `t` (scale factor `a`, c = 1, χ the comoving radial distance)
- `lusA2 Ω` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_lusA2`); its name is not checked (for `Ω : ℝ`): is defined as `Real.log 10 * (3 / 2 - 3 / 4 * Ω)`
- `lusA3 Ω` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_lusA3`); its name is not checked (for `Ω : ℝ`): is defined as `Real.log 10 ^ 2 * (9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6)`
- `redshift a t₀ t` — **PINNED** (pin theorem `redshiftCore_pins`): the redshift a(`t₀`)/a(`t`) − 1, observed at time `t₀`, of light emitted at time `t` (scale factor `a`)

## Author's paraphrase (hand-written; checked only by prose rules)

**B1, shape (normalisation-free).** In every flat ΛCDM model with `Ω ∈ [0.2, 0.4]`, with
sources at `z = 3` (time `t₃`) and `z = 7` (time `t₇`), the miss of the ΛCDM-implied cubic
log-polynomial at `z = 7` exceeds its miss at `z = 3` by more than 0.18 mag. A change of `H₀`
(or of any magnitude zero point) in the polynomial shifts both misses equally.

## Formal statement (Lean 4)

```lean
theorem cubic_shape_miss (Ω : ℝ) (hΩ₁ : 1 / 5 ≤ Ω) (hΩ₂ : Ω ≤ 2 / 5)
    (a : ℝ → ℝ) (t₇ t₃ t₀ : ℝ) (h₇₃ : t₇ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₇ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₇ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₇ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₃ : redshift a t₀ t₃ = 3) (hz₇ : redshift a t₀ t₇ = 7) :
    18 / 100 < 5 * Real.logb 10
        (lumDistFlat a t₀ t₇ / logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t₇))
      - 5 * Real.logb 10
        (lumDistFlat a t₀ t₃ / logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t₃)) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.BambaY.lumDistFlat`, `Cosmography.hubble`, `Cosmography.redshift`, `Cosmography.B1.logPolyDL3`, `Cosmography.B1.lusA2`, `Cosmography.B1.lusA3`, `Cosmography.BambaY.comoving`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: lumDistFlat, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): logPolyDL3², lusA2², lusA3².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `cubic_shape_miss`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): redshift(t₃) = 3; redshift(t₇) = 7.
- Source file: `Checked/Cosmography/B1Truncation.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 31
