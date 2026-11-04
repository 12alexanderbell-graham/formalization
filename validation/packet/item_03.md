# Item 03

**Area:** B1 fourth order

**Source:** see the claim

## Claim in plain words (the system's own text)

**Lusso et al. 2019, SNe + quasars + GRBs, central fit.** For every `Ω ∈ [0, 1]` and every scale
factor obeying `H = H₀ √(Ω(1+z)³ + 1 − Ω)` (with `H₀ > 0`) on the whole interval back to the farther
source, with sources at `1 + z = 2√2` and `1 + z = 4√2`, and every normalisation `H > 0`, the
quartic log-polynomial distance with the printed central coefficients `a₂ = 3.205`, `a₃ = 3.564`,
`a₄ = −2.510` (Table 2) has a residual distance modulus `5 log₁₀(d_L / D_L)` against the exact luminosity
distance `d_L` (`lumDistFlat`) that is larger at the farther source: the residual at
`1 + z = 4√2` exceeds the one at `1 + z = 2√2` by more than 3/10 mag. No normalisation and no
magnitude offset can remove this difference.

## Formal statement (Lean 4)

```lean
theorem l19_sqg_central (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1) (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)
    (H : ℝ) (hHp : 0 < H) :
    3 / 10 < 5 * Real.logb 10 (lumDistFlat a t₀ t₅
        / logPolyDL4 3.205 3.564 (-2.510) H (redshift a t₀ t₅))
      - 5 * Real.logb 10 (lumDistFlat a t₀ t₃
        / logPolyDL4 3.205 3.564 (-2.510) H (redshift a t₀ t₃)) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.BambaY.lumDistFlat`, `Cosmography.hubble`, `Cosmography.redshift`, `Cosmography.B1L19.logPolyDL4`, `Cosmography.B1.gL`, `Cosmography.BambaY.comoving`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: lumDistFlat, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): logPolyDL4².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `l19_sqg_central`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): logPolyDL4: a₂ = 3.205, a₃ = 3.564, a₄ = -2.510; redshift(t₃) = 2 * √2 - 1; redshift(t₅) = 4 * √2 - 1.
- Source file: `Checked/Cosmography/B1L19.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 03
