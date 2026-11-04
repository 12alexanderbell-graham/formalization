# Item 09

**Area:** B1 fourth order

**Source:** see the claim

## Claim in plain words (the system's own text)

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

See GLOSSARY.md: `Cosmography.BambaY.lumDistFlat`, `Cosmography.hubble`, `Cosmography.redshift`, `Cosmography.B1L19.logPolyDL4`, `Cosmography.B1.gL`, `Cosmography.BambaY.comoving`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: lumDistFlat, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): logPolyDL4².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `l19_sqg_box`.
- Source file: `Checked/Cosmography/B1L19.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 09
