# Item 59

**Area:** B1

**Source:** Risaliti & Lusso, Nat. Astron. 3, 272 (2019); Lusso et al., A&A 628, L4 (2019), Eq. (8): third-order log-polynomial distance and its ΛCDM-implied coefficients

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `Ω : ℝ`, `a : ℝ → ℝ`, `t : ℝ`, `t₀ : ℝ`:

**assuming**

1. `1 / 5 ≤ Ω`
2. `Ω ≤ 2 / 5`
3. `t ≤ t₀`
4. for every `s : ℝ`, if `s ∈ Set.Icc t t₀`, then `0 < a s`
5. for every `s : ℝ`, if `s ∈ Set.Icc t t₀`, then `DifferentiableAt ℝ a s`
6. `0 < hubble a t₀`
7. for every `s : ℝ`, if `s ∈ Set.Icc t t₀`, then `hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω)`
8. `redshift a t₀ t = 7`

**then**

1. `0 < logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t)`
2. `3 / 10 < 5 * Real.logb 10 (lumDistFlat a t₀ t / logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t))`

Program definitions in this claim:

- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): phrase (hand-written, linted): the Hubble rate with the scale factor `a` and the cosmic time of evaluation `t` (logarithmic derivative of the scale factor with respect to cosmic time; positive for expansion and negative for contraction); by definition, `hubble a t` is `deriv a t / a t`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «logarithmic derivative of the scale factor with respect to cosmic time» only assuming `0 < a t`; `DifferentiableAt ℝ a t`, «positive for expansion and negative for contraction» only assuming `0 < a t`; `0 < deriv a t`, «positive for expansion and negative for contraction» only assuming `0 < a t`; `deriv a t < 0`
- `logPolyDL3 a₂ a₃ H₀ z` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_logPolyDL3`); its name is not checked (for `a₂ : ℝ`, `a₃ : ℝ`, `H₀ : ℝ`, `z : ℝ`): is defined as `Real.log 10 / H₀ * (Real.logb 10 (1 + z) + a₂ * Real.logb 10 (1 + z) ^ 2 + a₃ * Real.logb 10 (1 + z) ^ 3)`
- `lumDistFlat a t₀ t` — **PINNED** (pin theorem `lumDistFlat_pins`): phrase (hand-written, linted): the luminosity distance in flat FLRW with the scale factor `a`, the observation time `t₀` and the emission time `t` (units in which the speed of light is one); by definition, `lumDistFlat a t₀ t` is `a t₀ * (1 + redshift a t₀ t) * comoving a t₀ t`
- `lusA2 Ω` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_lusA2`); its name is not checked (for `Ω : ℝ`): is defined as `Real.log 10 * (3 / 2 - 3 / 4 * Ω)`
- `lusA3 Ω` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_lusA3`); its name is not checked (for `Ω : ℝ`): is defined as `Real.log 10 ^ 2 * (9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6)`
- `redshift a t₀ t` — **PINNED** (pin theorem `redshiftCore_pins`): phrase (hand-written, linted): the cosmological redshift with the scale factor `a`, the observation time `t₀` and the emission time `t` (positive when emission precedes observation in an expanding universe; one plus redshift is the scale factor at observation over that at emission; negative redshift is blueshift; zero when emission and observation coincide); by definition, `redshift a t₀ t` is `a t₀ / a t - 1`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «positive when emission precedes observation in an expanding universe» only assuming for every `s : ℝ`, `0 < a s`; `StrictMono a`; `t < t₀`, «one plus redshift is the scale factor at observation over that at emission», «zero when emission and observation coincide» only assuming `a t₀ ≠ 0`

## Author's paraphrase (hand-written; checked only by prose rules)

**B1, z = 7.** As `cubic_misses_z3`, at `z = 7`: more than 0.3 mag.

## Formal statement (Lean 4)

```lean
theorem cubic_misses_z7 (Ω : ℝ) (hΩ₁ : 1 / 5 ≤ Ω) (hΩ₂ : Ω ≤ 2 / 5)
    (a : ℝ → ℝ) (t t₀ : ℝ) (htt : t ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz : redshift a t₀ t = 7) :
    0 < logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t) ∧
    3 / 10 < 5 * Real.logb 10
      (lumDistFlat a t₀ t / logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t)) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.BambaY.lumDistFlat`, `Cosmography.hubble`, `Cosmography.redshift`, `Cosmography.B1.logPolyDL3`, `Cosmography.B1.lusA2`, `Cosmography.B1.lusA3`, `Cosmography.BambaY.comoving`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: lumDistFlat, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): logPolyDL3², lusA2², lusA3².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `cubic_misses_z7`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): redshift(t) = 7.
- Source file: `Checked/Cosmography/B1Truncation.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 59
