# Item 16

**Area:** Chemistry

**Source:** generalized two-parameter cubic equation of state: van der Waals (1873), Redlich & Kwong, Chem. Rev. 44, 233 (1949), Soave, Chem. Eng. Sci. 27, 1197 (1972), Peng & Robinson, Ind. Eng. Chem. Fundam. 15, 59 (1976)

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `R : ℝ`, `a : ℝ`, `b : ℝ`, `T : ℝ`, `v : ℝ`:

**assuming**

1. `0 < a`
2. `0 < b`
3. `b < v`
4. the critical point condition of an isotherm holds for the isotherm pressure function of molar volume `p := cubicP R a b 0 0 T` at the molar volume at the point `v` (pressure as a function of molar volume at fixed temperature): its first and second derivatives vanish at `v`

**then**

1. `cubicP R a b 0 0 T v * v / (R * T) = 3 / 8`
2. `b * cubicP R a b 0 0 T v / (R * T) = 1 / 8`
3. `a * cubicP R a b 0 0 T v / (R * T) ^ 2 = 27 / 64`

Program definitions in this claim:

- `IsCriticalIsotherm p v` — **PINNED** (pin theorem `criticalSpec_pins`): phrase (hand-written, linted): the critical point condition of an isotherm holds for the isotherm pressure function of molar volume `p` at the molar volume at the point `v` (pressure as a function of molar volume at fixed temperature): its first and second derivatives vanish at `v`; by definition, means (`deriv p v = 0`) and (`deriv (deriv p) v = 0`)
- `cubicP R a b u w T v` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_cubicP`) (for `R : ℝ`, `a : ℝ`, `b : ℝ`, `u : ℝ`, `w : ℝ`, `T : ℝ`, `v : ℝ`): is defined as `R * T / (v - b) - a / (v ^ 2 + u * b * v + w * b ^ 2)`

## Author's paraphrase (hand-written; checked only by prose rules)

van der Waals: at every critical point, Z_c = 3/8, Ω_b = 1/8, Ω_a = 27/64 (exactly).

## Formal statement (Lean 4)

```lean
theorem vdW_constants (R a b T v : ℝ) (ha : 0 < a) (hb : 0 < b) (hv : b < v) (hc : IsCriticalIsotherm (cubicP R a b 0 0 T) v) :
    cubicP R a b 0 0 T v * v / (R * T) = 3 / 8 ∧ b * cubicP R a b 0 0 T v / (R * T) = 1 / 8 ∧
      a * cubicP R a b 0 0 T v / (R * T) ^ 2 = 27 / 64 := …
```

## Definitions it uses

See GLOSSARY.md: `Chemistry.CubicEOS.IsCriticalIsotherm`, `Chemistry.CubicEOS.cubicP`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsCriticalIsotherm.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `vdW_constants`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cubicP: u = 0, w = 0.
- Source file: `Checked/Chemistry/CubicEOS.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 16
