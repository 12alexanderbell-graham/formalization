# Item 23

**Area:** F2

**Source:** Capozziello, Lazkoz, Salzano, PRD 84, 124061 (2011), arXiv:1104.3096 (v1 and v2), Eq. (22): flat matter + CPL l₀, w_a² term missing a factor 9

## Claim in plain words (the system's own text)

Local existence of a smooth expanding scale factor for a smooth expansion law.

## Formal statement (Lean 4)

```lean
theorem exists_local_model (E : ℝ → ℝ) (hE : ContDiffAt ℝ 5 E 1) :
    ∃ a : ℝ → ℝ, a 0 = 1 ∧ ContDiffAt ℝ 5 a 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), 0 < a t ∧ HasDerivAt a (a t * E (a t)) t := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `exists_local_model`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Cosmography/CPLExistence.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 23
