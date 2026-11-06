# Item 30

**Area:** Chemistry

**Source:** generalized two-parameter cubic equation of state: van der Waals (1873), Redlich & Kwong, Chem. Rev. 44, 233 (1949), Soave, Chem. Eng. Sci. 27, 1197 (1972), Peng & Robinson, Ind. Eng. Chem. Fundam. 15, 59 (1976)

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `R : ℝ`, `a : ℝ`, `b : ℝ`, `u : ℝ`, `w : ℝ`, `T : ℝ`, `v : ℝ`:

**assuming**

1. `0 < a`
2. `b < v`
3. `0 < v ^ 2 + u * b * v + w * b ^ 2`

**then**

- (the molar volume `v` is a critical point of the isotherm `cubicP R a b u w T` (pressure as a function of molar volume at fixed temperature): p′(`v`) = 0 and p″(`v`) = 0) if and only if ((`v ^ 3 - 3 * b * v ^ 2 - 3 * (u + w) * b ^ 2 * v - (u ^ 2 + u * w - w) * b ^ 3 = 0`) and (`R * T * (v ^ 2 + u * b * v + w * b ^ 2) ^ 2 = a * (v - b) ^ 2 * (2 * v + u * b)`))

Program definitions in this claim:

- `IsCriticalIsotherm p v` — **PINNED** (pin theorem `criticalSpec_pins`): the molar volume `v` is a critical point of the isotherm `p` (pressure as a function of molar volume at fixed temperature): p′(`v`) = 0 and p″(`v`) = 0
- `cubicP R a b u w T v` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_cubicP`) (for `R : ℝ`, `a : ℝ`, `b : ℝ`, `u : ℝ`, `w : ℝ`, `T : ℝ`, `v : ℝ`): is defined as `R * T / (v - b) - a / (v ^ 2 + u * b * v + w * b ^ 2)`

## Author's paraphrase (hand-written; checked only by prose rules)

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
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Chemistry/CubicEOS.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 30
