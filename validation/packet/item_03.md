# Item 03

**Area:** T1 fidelity

**Source:** standard FLRW cosmology definitions (e.g. Weinberg, Cosmology, 2008; Hogg 1999, astro-ph/9905116); the specification each definition is pinned by is in the statement

## Claim in plain words (the system's own text)

The program's master equation is the blind `Ḣ` equation with `R = curv a`.

## Formal statement (Lean 4)

```lean
theorem masterEq_iff_blind (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ) :
    MasterEq Ω a F t₀ t ↔ FRSecondEq Ω a F t₀ t (curv a) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.FRCosmo.MasterEq`, `Cosmography.FRCosmo.curv`, `Cosmography.FRCosmo.rhoM`, `Cosmography.hubble`, `Fidelity.DustDensity`, `Fidelity.FRSecondEq`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: MasterEq, curv.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `masterEq_iff_blind`.
- Source file: `Checked/Fidelity/FRSpecs.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 03
