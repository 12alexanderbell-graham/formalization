# Item 05

**Area:** F2

**Source:** Capozziello, Lazkoz, Salzano, PRD 84, 124061 (2011), arXiv:1104.3096 (v1 and v2), Eq. (22): flat matter + CPL l₀, w_a² term missing a factor 9

## Claim in plain words (the system's own text)

**Cosmographic coefficients of flat matter + CPL** (correct version of CLS Eqs. (19)–(22)).
q₀, j₀ as printed; s₀ as printed with the dropped minus sign before `27/4` restored; l₀ with
`9 (7 − Ω)` in place of the printed `(7 − Ω)` in the `wₐ²` term.

## Formal statement (Lean 4)

```lean
theorem flatCPL_coeffs (Ω w₀ wₐ : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (hL : IsFlatCPL Ω w₀ wₐ a t₀)
    (hs : ContDiffAt ℝ 5 a t₀) :
    decel a t₀ = 1 / 2 + 3 / 2 * (1 - Ω) * w₀ ∧
    cosmoCoeff 3 a t₀ = 1 + 3 / 2 * (1 - Ω) * (3 * w₀ * (1 + w₀) + wₐ) ∧
    cosmoCoeff 4 a t₀ = -7 / 2 - 33 / 4 * (1 - Ω) * wₐ
      - 9 / 4 * (1 - Ω) * (9 + (7 - Ω) * wₐ) * w₀ - 9 / 4 * (1 - Ω) * (16 - 3 * Ω) * w₀ ^ 2
      - 27 / 4 * (1 - Ω) * (3 - Ω) * w₀ ^ 3 ∧
    cosmoCoeff 5 a t₀ = 35 / 2 + (1 - Ω) / 4 * (213 + 9 * (7 - Ω) * wₐ) * wₐ
      + (1 - Ω) / 4 * (489 + 9 * (82 - 21 * Ω) * wₐ) * w₀
      + 9 / 2 * (1 - Ω) * (67 - 21 * Ω + 3 / 2 * (23 - 11 * Ω) * wₐ) * w₀ ^ 2
      + 27 / 4 * (1 - Ω) * (47 - 24 * Ω) * w₀ ^ 3
      + 81 / 2 * (1 - Ω) * (3 - 2 * Ω) * w₀ ^ 4 := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.CPL.IsFlatCPL`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.redshift`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, IsFlatCPL, decel.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `flatCPL_coeffs`.
- Source file: `Checked/Cosmography/CPLCoefficients.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 05
