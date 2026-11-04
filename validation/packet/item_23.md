# Item 23

**Area:** F2

**Source:** Capozziello, Lazkoz, Salzano, PRD 84, 124061 (2011), arXiv:1104.3096 (v1 and v2), Eq. (22): flat matter + CPL l₀, w_a² term missing a factor 9

## Claim in plain words (the system's own text)

**Flat matter + CPL models exist for every Ω, w₀, wₐ** (at `t₀ = 0`, `C⁵` there).

## Formal statement (Lean 4)

```lean
theorem exists_flatCPL (Ω w₀ wₐ : ℝ) :
    ∃ a : ℝ → ℝ, IsFlatCPL Ω w₀ wₐ a 0 ∧ ContDiffAt ℝ 5 a 0 := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.CPL.IsFlatCPL`, `Cosmography.hubble`, `Cosmography.redshift`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsFlatCPL.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Source file: `Checked/Cosmography/CPLExistence.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 23
