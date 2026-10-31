# Item 22

**Area:** F2

**Source:** Capozziello, Lazkoz, Salzano, PRD 84, 124061 (2011), arXiv:1104.3096 (v1 and v2), Eq. (22): flat matter + CPL l₀, w_a² term missing a factor 9

## Claim in plain words (the system's own text)

**The printed l₀ of CLS Eq. (22) is false at every parameter point with
`(1 − Ω)(7 − Ω) wₐ ≠ 0`**: there is a flat CPL model with those parameters whose l₀ differs.

## Formal statement (Lean 4)

```lean
theorem printedL0_false_at (Ω w₀ wₐ : ℝ) (hne : (1 - Ω) * (7 - Ω) * wₐ ≠ 0) :
    ∃ a : ℝ → ℝ, IsFlatCPL Ω w₀ wₐ a 0 ∧ ContDiffAt ℝ 5 a 0 ∧
      cosmoCoeff 5 a 0 ≠ 35 / 2 + (1 - Ω) / 4 * (213 + (7 - Ω) * wₐ) * wₐ
        + (1 - Ω) / 4 * (489 + 9 * (82 - 21 * Ω) * wₐ) * w₀
        + 9 / 2 * (1 - Ω) * (67 - 21 * Ω + 3 / 2 * (23 - 11 * Ω) * wₐ) * w₀ ^ 2
        + 27 / 4 * (1 - Ω) * (47 - 24 * Ω) * w₀ ^ 3
        + 81 / 2 * (1 - Ω) * (3 - 2 * Ω) * w₀ ^ 4 := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.CPL.IsFlatCPL`, `Cosmography.hubble`, `Cosmography.redshift`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, IsFlatCPL.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `cpl_printedL0_false_at`.
- Source file: `Checked/Cosmography/CPLExistence.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 22
