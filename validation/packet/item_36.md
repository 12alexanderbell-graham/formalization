# Item 36

**Area:** C27 at fit level

**Source:** see the claim

## Claim in plain words (the system's own text)

**C27 (fit level).** For every `Ω ∈ [0, 1]`, no cubic log-polynomial with `a₂ ∈ [3.43, 3.49]`,
`a₃ ∈ [1.57, 1.69]` (the RL19 Fig. 3 contour centre with its reading uncertainty), normalisation
`H > 0`, positive at `1 + z = √2, 2√2, 4√2`, agrees with the exact distance modulus of a model
obeying `H = H₀√(Ω(1+z)³ + 1 − Ω)` within 0.05 mag up to a common offset at all three redshifts.

## Formal statement (Lean 4)

```lean
theorem rl19_box_unmatched (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₅ t₃ t₁ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₁ : t₃ ≤ t₁) (h₁₀ : t₁ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₁ : redshift a t₀ t₁ = √2 - 1) (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1)
    (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)
    (a₂ a₃ H c : ℝ) (ha₂l : 343 / 100 ≤ a₂) (ha₂u : a₂ ≤ 349 / 100)
    (ha₃l : 157 / 100 ≤ a₃) (ha₃u : a₃ ≤ 169 / 100) (hHp : 0 < H)
    (hp₁ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₁))
    (hp₃ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₃))
    (hp₅ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₅)) :
    ¬ (|5 * Real.logb 10 (lumDistFlat a t₀ t₁ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₁)) - c|
          ≤ 1 / 20 ∧
        |5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₃)) - c|
          ≤ 1 / 20 ∧
        |5 * Real.logb 10 (lumDistFlat a t₀ t₅ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₅)) - c|
          ≤ 1 / 20) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.BambaY.lumDistFlat`, `Cosmography.hubble`, `Cosmography.redshift`, `Cosmography.B1.logPolyDL3`, `Cosmography.BambaY.comoving`, `changed;.Checked.Chemistry.CoexistenceReduced.q`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: lumDistFlat, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): logPolyDL3².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `rl19_box_unmatched`.
- Source file: `Checked/Cosmography/B1FitRL19.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 36
