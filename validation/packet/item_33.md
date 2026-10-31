# Item 33

**Area:** Chemistry

**Source:** generalized two-parameter cubic equation of state: van der Waals (1873), Redlich & Kwong, Chem. Rev. 44, 233 (1949), Soave, Chem. Eng. Sci. 27, 1197 (1972), Peng & Robinson, Ind. Eng. Chem. Fundam. 15, 59 (1976)

## Claim in plain words (the system's own text)

Critical-point conditions of the generalized cubic EOS, in closed form.

## Formal statement (Lean 4)

```lean
theorem isCritical_iff (R a b u w T v : ℝ) (ha : 0 < a) (hv : b < v) (hD : 0 < v ^ 2 + u * b * v + w * b ^ 2) :
    IsCriticalIsotherm (cubicP R a b u w T) v ↔
      (v ^ 3 - 3 * b * v ^ 2 - 3 * (u + w) * b ^ 2 * v - (u ^ 2 + u * w - w) * b ^ 3 = 0 ∧
        R * T * (v ^ 2 + u * b * v + w * b ^ 2) ^ 2 = a * (v - b) ^ 2 * (2 * v + u * b)) := …
```

## Definitions it uses

See GLOSSARY.md: `Chemistry.CubicEOS.IsCriticalIsotherm`, `Chemistry.CubicEOS.cubicP`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsCriticalIsotherm.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `isCritical_iff`.
- Source file: `Checked/Chemistry/CubicEOS.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 33
