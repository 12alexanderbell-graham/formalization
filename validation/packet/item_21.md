# Item 21

**Area:** Chemistry

**Source:** generalized two-parameter cubic equation of state: van der Waals (1873), Redlich & Kwong, Chem. Rev. 44, 233 (1949), Soave, Chem. Eng. Sci. 27, 1197 (1972), Peng & Robinson, Ind. Eng. Chem. Fundam. 15, 59 (1976)

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `R : ℝ`, `A : ℝ`, `b : ℝ`, `Tc : ℝ`, `vc : ℝ`, `vl : ℝ`, `vg : ℝ`, `ps : ℝ`:

**assuming**

1. `0 < R`
2. `0 < A`
3. `0 < b`
4. `0 < Tc`
5. `b < vc`
6. the molar volume `vc` is a critical point of the isotherm `cubicP R (A / √Tc) b 1 0 Tc` (pressure as a function of molar volume at fixed temperature): p′(`vc`) = 0 and p″(`vc`) = 0
7. `b < vl`
8. the molar volumes `vl` < `vg` are in Maxwell coexistence on the isotherm `cubicP R (A / √(7 / 10 * Tc)) b 1 0 (7 / 10 * Tc)` at pressure `ps`: p(`vl`) = p(`vg`) = `ps` and the integral of p from `vl` to `vg` equals `ps`·(`vg` − `vl`)

**then**

1. `RoundsTo (ps / cubicP R (A / √Tc) b 1 0 Tc vc) 87e-3 3`
2. `RoundsTo (acentric ps (cubicP R (A / √Tc) b 1 0 Tc vc)) 58e-3 3`

Program definitions in this claim:

- `IsCriticalIsotherm p v` — **PINNED** (pin theorem `criticalSpec_pins`): the molar volume `v` is a critical point of the isotherm `p` (pressure as a function of molar volume at fixed temperature): p′(`v`) = 0 and p″(`v`) = 0
- `IsMaxwellCoexistence p vl vg ps` — **PINNED** (pin theorem `maxwellSpec_pins`): the molar volumes `vl` < `vg` are in Maxwell coexistence on the isotherm `p` at pressure `ps`: p(`vl`) = p(`vg`) = `ps` and the integral of p from `vl` to `vg` equals `ps`·(`vg` − `vl`)
- `RoundsTo x d k` — MATH, not pinned, so only the formula shown is checked, not its name (for `x : ℝ`, `d : ℝ`, `k : ℕ`): means `|x - d| ≤ 1 / (2 * 10 ^ k)`
- `acentric ps pc` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_acentric`) (for `ps : ℝ`, `pc : ℝ`): is defined as `-Real.logb 10 (ps / pc) - 1`
- `cubicP R a b u w T v` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_cubicP`) (for `R : ℝ`, `a : ℝ`, `b : ℝ`, `u : ℝ`, `w : ℝ`, `T : ℝ`, `v : ℝ`): is defined as `R * T / (v - b) - a / (v ^ 2 + u * b * v + w * b ^ 2)`

## Author's paraphrase (hand-written; checked only by prose rules)

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

## Your answers: use ANSWER_FORM.md, item 21
