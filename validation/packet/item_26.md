# Item 26

**Area:** Chemistry

**Source:** generalized two-parameter cubic equation of state: van der Waals (1873), Redlich & Kwong, Chem. Rev. 44, 233 (1949), Soave, Chem. Eng. Sci. 27, 1197 (1972), Peng & Robinson, Ind. Eng. Chem. Fundam. 15, 59 (1976)

## Claim in plain words (the system's own text)

Peng–Robinson: at every critical point, Z_c = 0.3074 (four decimals), Ω_b = 0.07780 and
Ω_a = 0.45724 (five decimals).

## Formal statement (Lean 4)

```lean
theorem pr_constants (R a b T v : ℝ) (ha : 0 < a) (hb : 0 < b) (hv : b < v) (hc : IsCriticalIsotherm (cubicP R a b 2 (-1) T) v) :
    RoundsTo (cubicP R a b 2 (-1) T v * v / (R * T)) 0.3074 4 ∧
      RoundsTo (b * cubicP R a b 2 (-1) T v / (R * T)) 0.07780 5 ∧
      RoundsTo (a * cubicP R a b 2 (-1) T v / (R * T) ^ 2) 0.45724 5 := …
```

## Definitions it uses

See GLOSSARY.md: `Chemistry.CubicEOS.IsCriticalIsotherm`, `Chemistry.CubicEOS.cubicP`, `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsCriticalIsotherm.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `pr_constants`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cubicP: u = 2, w = -1; RoundsTo: d = 0.3074, k = 4, d = 0.07780, k = 5, d = 0.45724.
- Source file: `Checked/Chemistry/CubicEOS.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 26
