# Item 49

**Area:** B1 fourth order

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `Ω : ℝ`, `a : ℝ → ℝ`, `t₅ : ℝ`, `t₃ : ℝ`, `t₀ : ℝ`, `a₂ : ℝ`, `a₃ : ℝ`, `a₄ : ℝ`, `H : ℝ`:

**assuming**

1. `0 ≤ Ω`
2. `Ω ≤ 1`
3. `t₅ ≤ t₃`
4. `t₃ ≤ t₀`
5. for every `s : ℝ`, if `s ∈ Set.Icc t₅ t₀`, then `0 < a s`
6. for every `s : ℝ`, if `s ∈ Set.Icc t₅ t₀`, then `DifferentiableAt ℝ a s`
7. `0 < hubble a t₀`
8. for every `s : ℝ`, if `s ∈ Set.Icc t₅ t₀`, then `hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω)`
9. `redshift a t₀ t₃ = 2 * √2 - 1`
10. `redshift a t₀ t₅ = 4 * √2 - 1`
11. `0 < H`
12. `3.043 ≤ a₂`
13. `a₃ ≤ 4.480`
14. `a₄ ≤ -0.915`
15. `0 < logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₅)`

**then**

- `5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₃)) < 5 * Real.logb 10 (lumDistFlat a t₀ t₅ / logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₅))`

Program definitions in this claim:

- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): phrase (hand-written, linted): the Hubble rate with the scale factor `a` and the cosmic time of evaluation `t` (logarithmic derivative of the scale factor with respect to cosmic time; positive for expansion and negative for contraction); by definition, `hubble a t` is `deriv a t / a t`
- `logPolyDL4 a₂ a₃ a₄ H₀ z` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_logPolyDL4`); its name is not checked (for `a₂ : ℝ`, `a₃ : ℝ`, `a₄ : ℝ`, `H₀ : ℝ`, `z : ℝ`): is defined as `Real.log 10 / H₀ * (Real.logb 10 (1 + z) + a₂ * Real.logb 10 (1 + z) ^ 2 + a₃ * Real.logb 10 (1 + z) ^ 3 + a₄ * Real.logb 10 (1 + z) ^ 4)`
- `lumDistFlat a t₀ t` — **PINNED** (pin theorem `lumDistFlat_pins`): phrase (hand-written, linted): the luminosity distance in flat FLRW with the scale factor `a`, the observation time `t₀` and the emission time `t` (units in which the speed of light is one); by definition, `lumDistFlat a t₀ t` is `a t₀ * (1 + redshift a t₀ t) * comoving a t₀ t`
- `redshift a t₀ t` — **PINNED** (pin theorem `redshiftCore_pins`): phrase (hand-written, linted): the cosmological redshift with the scale factor `a`, the observation time `t₀` and the emission time `t` (positive when emission precedes observation in an expanding universe; one plus redshift is the scale factor at observation over that at emission; negative redshift is blueshift; zero when emission and observation coincide); by definition, `redshift a t₀ t` is `a t₀ / a t - 1`

## Author's paraphrase (hand-written; checked only by prose rules)

**Lusso et al. 2019, SNe + quasars + GRBs, the whole 1σ range.** For every `Ω ∈ [0, 1]` and
every scale factor obeying `H = H₀ √(Ω(1+z)³ + 1 − Ω)` (with `H₀ > 0`) on the whole interval back to
the farther source, with sources at `1 + z = 2√2` and `1 + z = 4√2`, every quartic log-polynomial
distance with `a₂ ≥ 3.043`, `a₃ ≤ 4.480`, `a₄ ≤ −0.915` (the printed Table 2 ends of the 1σ ranges
on the side that brings the quartic's distance ratio closer to the exact one; the region contains the box of all three printed ±1σ ranges),
normalisation `H > 0` and positive at the farther source has a residual distance modulus
`5 log₁₀(d_L / D_L)` against the exact luminosity distance `d_L` (`lumDistFlat`) that is strictly
larger at `1 + z = 4√2` than at `1 + z = 2√2`.

## Formal statement (Lean 4)

```lean
theorem l19_sqg_box (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1) (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)
    (a₂ a₃ a₄ H : ℝ) (hHp : 0 < H)
    (ha₂ : 3.043 ≤ a₂) (ha₃ : a₃ ≤ 4.480) (ha₄ : a₄ ≤ -0.915)
    (hp₅ : 0 < logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₅)) :
    5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₃))
      < 5 * Real.logb 10 (lumDistFlat a t₀ t₅ / logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₅)) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.BambaY.lumDistFlat`, `Cosmography.hubble`, `Cosmography.redshift`, `Cosmography.B1L19.logPolyDL4`, `Cosmography.BambaY.comoving`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: lumDistFlat, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): logPolyDL4².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `l19_sqg_box`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): redshift(t₃) = 2 * √2 - 1; redshift(t₅) = 4 * √2 - 1.
- Source file: `Checked/Cosmography/B1L19.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 49
