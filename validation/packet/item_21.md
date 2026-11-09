# Item 21

**Area:** Chemistry

**Source:** generalized two-parameter cubic equation of state: van der Waals (1873), Redlich & Kwong, Chem. Rev. 44, 233 (1949), Soave, Chem. Eng. Sci. 27, 1197 (1972), Peng & Robinson, Ind. Eng. Chem. Fundam. 15, 59 (1976)

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `R : ℝ`, `a : ℝ`, `b : ℝ`, `T : ℝ`, `v : ℝ`:

**assuming**

1. `0 < a`
2. `0 < b`
3. `b < v`
4. the isotherm pressure function of molar volume `p := cubicP R a b 1 0 T` satisfies the critical point condition of an isotherm with the molar volume at the point `v` (pressure as a function of molar volume at fixed temperature; first and second volume derivatives of pressure both vanish; a mere stationary point is not critical)

**then**

1. `cubicP R a b 1 0 T v * v / (R * T) = 1 / 3`
2. `RoundsTo (b * cubicP R a b 1 0 T v / (R * T)) 7780e-5 5`
3. `RoundsTo (a * cubicP R a b 1 0 T v / (R * T) ^ 2) 0.42748 5`

Program definitions in this claim:

- `IsCriticalIsotherm p v` — **PINNED** (pin theorem `criticalSpec_pins`): phrase (hand-written, linted): the isotherm pressure function of molar volume `p` satisfies the critical point condition of an isotherm with the molar volume at the point `v` (pressure as a function of molar volume at fixed temperature; first and second volume derivatives of pressure both vanish; a mere stationary point is not critical); by definition, means (`deriv p v = 0`) and (`deriv (deriv p) v = 0`)
- `RoundsTo x d k` — MATH, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_RoundsTo`) (for `x : ℝ`, `d : ℝ`, `k : ℕ`): means `|x - d| ≤ 1 / (2 * 10 ^ k)`
- `cubicP R a b u w T v` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_cubicP`) (for `R : ℝ`, `a : ℝ`, `b : ℝ`, `u : ℝ`, `w : ℝ`, `T : ℝ`, `v : ℝ`): is defined as `R * T / (v - b) - a / (v ^ 2 + u * b * v + w * b ^ 2)`

## Author's paraphrase (hand-written; checked only by prose rules)

Redlich–Kwong / Soave–Redlich–Kwong: at every critical point, Z_c = 1/3 exactly,
Ω_b = 0.07780 and Ω_a = 0.42748 to five decimals.

## Formal statement (Lean 4)

```lean
theorem rk_constants (R a b T v : ℝ) (ha : 0 < a) (hb : 0 < b) (hv : b < v) (hc : IsCriticalIsotherm (cubicP R a b 1 0 T) v) :
    cubicP R a b 1 0 T v * v / (R * T) = 1 / 3 ∧
      RoundsTo (b * cubicP R a b 1 0 T v / (R * T)) 0.07780 5 ∧
      RoundsTo (a * cubicP R a b 1 0 T v / (R * T) ^ 2) 0.42748 5 := …
```

## Definitions it uses

See GLOSSARY.md: `Chemistry.CubicEOS.IsCriticalIsotherm`, `Chemistry.CubicEOS.cubicP`, `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsCriticalIsotherm.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `rk_constants`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cubicP: u = 1, w = 0; RoundsTo: d = 0.08664, k = 5, d = 0.42748.
- Source file: `Checked/Chemistry/CubicEOS.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 21
