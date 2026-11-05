# Item 03

**Area:** B1 fourth order

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `Ω : ℝ`, `K : ℝ`, `a : ℝ → ℝ`, `t₅ : ℝ`, `t₃ : ℝ`, `t₀ : ℝ`, `H : ℝ`:

**assuming**

1. `1 / 10 ≤ Ω`
2. `Ω ≤ 1`
3. `t₅ ≤ t₃`
4. `t₃ ≤ t₀`
5. for every `s : ℝ`, if `s ∈ Set.Icc t₅ t₀`, then `0 < a s`
6. for every `s : ℝ`, if `s ∈ Set.Icc t₅ t₀`, then `DifferentiableAt ℝ a s`
7. `0 < hubble a t₀`
8. `1 ≤ omega0 K a t₀`
9. `omega0 K a t₀ ≤ 11 / 10`
10. for every `s : ℝ`, if `s ∈ Set.Icc t₅ t₀`, then `hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + (1 - omega0 K a t₀) * (1 + redshift a t₀ s) ^ 2 + omega0 K a t₀ - Ω)`
11. `redshift a t₀ t₃ = 2 * √2 - 1`
12. `redshift a t₀ t₅ = 4 * √2 - 1`
13. `0 < H`

**then**

- `3 / 20 < 5 * Real.logb 10 (lumDist K a t₀ t₅ / logPolyDL4 3.205 3.564 (-2.510) H (redshift a t₀ t₅)) - 5 * Real.logb 10 (lumDist K a t₀ t₃ / logPolyDL4 3.205 3.564 (-2.510) H (redshift a t₀ t₃))`

Program definitions in this claim:

- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): the Hubble rate a′(t)/a(t) of the scale factor `a` at time `t`
- `logPolyDL4 a₂ a₃ a₄ H₀ z` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_logPolyDL4`); its name is not checked (for `a₂ : ℝ`, `a₃ : ℝ`, `a₄ : ℝ`, `H₀ : ℝ`, `z : ℝ`): is defined as `Real.log 10 / H₀ * (Real.logb 10 (1 + z) + a₂ * Real.logb 10 (1 + z) ^ 2 + a₃ * Real.logb 10 (1 + z) ^ 3 + a₄ * Real.logb 10 (1 + z) ^ 4)`
- `lumDist K a t₀ t` — **PINNED** (pin theorem `lumDistSpec2_pins`): the luminosity distance a(t₀)·(1 + z)·S_K(χ), at observation time `t₀`, of a source emitting at time `t`, in the FLRW model with scale factor `a` and curvature constant `K` (c = 1; z the redshift, χ the comoving radial distance, S_K the transverse factor)
- `omega0 K a t₀` — **PINNED** (pin theorem `omega0Spec_pins`): the total density parameter Ω₀ = 1 + K/(H₀²·a₀²) at time `t₀` for curvature constant `K` and scale factor `a` (c = 1; H₀, a₀ the Hubble rate and scale factor at `t₀`; Ω_k = 1 − Ω₀)
- `redshift a t₀ t` — **PINNED** (pin theorem `redshiftCore_pins`): the redshift a(`t₀`)/a(`t`) − 1, observed at time `t₀`, of light emitted at time `t` (scale factor `a`)

## Author's paraphrase (hand-written; checked only by prose rules)

**Lusso et al. 2019, SNe + quasars + GRBs, central fit, closed or flat curvature.** For every matter
density `Ω ∈ [1/10, 1]`, every curvature constant `K` whose total density parameter
`Ω₀ = 1 + K/(H₀²a₀²)` lies in `[1, 11/10]`, and every scale factor obeying
`H = H₀ √(Ω(1+z)³ + (1 − Ω₀)(1+z)² + Ω₀ − Ω)` (with `H₀ > 0`) on the whole interval back to the
farther source, with sources at `1 + z = 2√2` and `1 + z = 4√2`, and every normalisation `H > 0`,
the quartic log-polynomial distance with the printed central coefficients `a₂ = 3.205`,
`a₃ = 3.564`, `a₄ = −2.510` has a residual distance modulus `5 log₁₀(d_L / D_L)` against the exact
luminosity distance `d_L` (`lumDist K`) that exceeds at `1 + z = 4√2` the one at `1 + z = 2√2` by
more than 3/20 mag.

## Formal statement (Lean 4)

```lean
theorem l19_sqg_curved (Ω K : ℝ) (hΩ₀ : 1 / 10 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hK₀ : 1 ≤ omega0 K a t₀) (hK₁ : omega0 K a t₀ ≤ 11 / 10)
    (hH : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3
        + (1 - omega0 K a t₀) * (1 + redshift a t₀ s) ^ 2 + omega0 K a t₀ - Ω))
    (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1) (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)
    (H : ℝ) (hHp : 0 < H) :
    3 / 20 < 5 * Real.logb 10 (lumDist K a t₀ t₅
        / logPolyDL4 3.205 3.564 (-2.510) H (redshift a t₀ t₅))
      - 5 * Real.logb 10 (lumDist K a t₀ t₃
        / logPolyDL4 3.205 3.564 (-2.510) H (redshift a t₀ t₃)) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.BambaK.lumDist`, `Cosmography.BambaK.omega0`, `Cosmography.hubble`, `Cosmography.redshift`, `Cosmography.B1L19.logPolyDL4`, `Cosmography.BambaY.comoving`, `Cosmography.Transverse.transverse`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: lumDist, omega0, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): logPolyDL4².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `l19_sqg_curved`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): logPolyDL4: a₂ = 3.205, a₃ = 3.564, a₄ = -2.510; redshift(t₃) = 2 * √2 - 1; redshift(t₅) = 4 * √2 - 1.
- Source file: `Checked/Cosmography/B1L19Curved.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 03
