# Item 10

**Area:** Chemistry

**Source:** generalized two-parameter cubic equation of state: van der Waals (1873), Redlich & Kwong, Chem. Rev. 44, 233 (1949), Soave, Chem. Eng. Sci. 27, 1197 (1972), Peng & Robinson, Ind. Eng. Chem. Fundam. 15, 59 (1976)

## Claim in plain words (the system's own text)

Redlich–Kwong fluid (pressure RT/(v−b) − A/(√T v(v+b))): at any critical point (T_c > 0,
v_c > b) and at T = 0.7 T_c, every Maxwell coexistence state with liquid volume above the
co-volume b has pressure 0.087 times the critical pressure (3 decimals) and acentric factor
0.058 (3 decimals).

## Formal statement (Lean 4)

```lean
theorem rk_coexistence_unique (R A b Tc vc vl vg ps : ℝ) (hR : 0 < R) (hA : 0 < A) (hb : 0 < b)
    (hTc : 0 < Tc) (hvc : b < vc)
    (hc : IsCriticalIsotherm (cubicP R (A / Real.sqrt Tc) b 1 0 Tc) vc)
    (hl : b < vl)
    (h : IsMaxwellCoexistence
      (cubicP R (A / Real.sqrt (7 / 10 * Tc)) b 1 0 (7 / 10 * Tc)) vl vg ps) :
    RoundsTo (ps / cubicP R (A / Real.sqrt Tc) b 1 0 Tc vc) 0.087 3 ∧
      RoundsTo (acentric ps (cubicP R (A / Real.sqrt Tc) b 1 0 Tc vc)) 0.058 3 := …
```

## Definitions it uses

See GLOSSARY.md: `Chemistry.Coexistence.IsMaxwellCoexistence`, `Chemistry.CubicEOS.IsCriticalIsotherm`, `Chemistry.Coexistence.acentric`, `Chemistry.CubicEOS.cubicP`, `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsMaxwellCoexistence, IsCriticalIsotherm.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `rk_coexistence_unique`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cubicP: u = 1, w = 0; RoundsTo: d = 0.087, k = 3, d = 0.058.
- Source file: `Checked/Chemistry/RKAcentric.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 10
