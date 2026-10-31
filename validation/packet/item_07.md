# Item 07

**Area:** Chemistry

**Source:** generalized two-parameter cubic equation of state: van der Waals (1873), Redlich & Kwong, Chem. Rev. 44, 233 (1949), Soave, Chem. Eng. Sci. 27, 1197 (1972), Peng & Robinson, Ind. Eng. Chem. Fundam. 15, 59 (1976)

## Claim in plain words (the system's own text)

The critical cubic has exactly one root above 1 (x = v_c/b > 1).

## Formal statement (Lean 4)

```lean
theorem critCubic_existsUnique (u w : ℝ) (hu : -2 < u) (h1 : 0 < 1 + u + w) (h2 : u + w < -1) :
    ∃! x : ℝ, 1 < x ∧ critCubic u w x = 0 := …
```

## Definitions it uses

See GLOSSARY.md: `Chemistry.CubicEOS.critCubic`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `critCubic_existsUnique`.
- Source file: `Checked/Chemistry/CubicEOS.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 07
