# Item 47

**Area:** Chemistry

**Source:** generalized two-parameter cubic equation of state: van der Waals (1873), Redlich & Kwong, Chem. Rev. 44, 233 (1949), Soave, Chem. Eng. Sci. 27, 1197 (1972), Peng & Robinson, Ind. Eng. Chem. Fundam. 15, 59 (1976)

## Claim in plain words (the system's own text)

van der Waals fluid at T = 0.7 · 8a/(27Rb) (that is 0.7 T_c): every Maxwell coexistence state
with liquid volume above the co-volume b has pressure 0.20046 · a/(27b²) (that is 0.20046 P_c) to
five decimals (the saturation pressure is determined to that accuracy).

## Formal statement (Lean 4)

```lean
theorem vdW_coexistence_unique (R a b vl vg ps : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)
    (hl : b < vl)
    (h : IsMaxwellCoexistence (cubicP R a b 0 0 (7 / 10 * (8 * a / (27 * R * b)))) vl vg ps) :
    RoundsTo (ps / (a / (27 * b ^ 2))) 0.20046 5 := …
```

## Definitions it uses

See GLOSSARY.md: `Chemistry.Coexistence.IsMaxwellCoexistence`, `Chemistry.CubicEOS.cubicP`, `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsMaxwellCoexistence.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `vdW_coexistence_unique`.
- Source file: `Checked/Chemistry/Coexistence.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 47
