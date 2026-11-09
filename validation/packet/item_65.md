# Item 65

**Area:** Chemistry

**Source:** generalized two-parameter cubic equation of state: van der Waals (1873), Redlich & Kwong, Chem. Rev. 44, 233 (1949), Soave, Chem. Eng. Sci. 27, 1197 (1972), Peng & Robinson, Ind. Eng. Chem. Fundam. 15, 59 (1976)

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `R : ℝ`, `A : ℝ`, `b : ℝ`, `Tc : ℝ`, `v : ℝ` (renamed by the generator after the pinned slot it fills; the statement calls it `vc`), `vl : ℝ`, `vg : ℝ`, `ps : ℝ`:

**assuming**

1. `0 < R`
2. `0 < A`
3. `0 < b`
4. `0 < Tc`
5. `b < v`
6. the critical point condition of an isotherm holds for the isotherm pressure function of molar volume `p := cubicP R (A / √Tc) b 1 0 Tc` at the molar volume at the point `v` (pressure as a function of molar volume at fixed temperature): its first and second derivatives vanish at `v`
7. `b < vl`
8. the Maxwell equal area coexistence condition holds for the liquid molar volume `vl` and the gas molar volume `vg`, with `vl` below `vg`, on the isotherm pressure function of molar volume `p := cubicP R (A / √(7 / 10 * Tc)) b 1 0 (7 / 10 * Tc)` at the saturation pressure `ps`: the isotherm takes the value `ps` at both, and its integral from `vl` to `vg` equals `ps` times the volume difference

**then**

1. `RoundsTo (ps / cubicP R (A / √Tc) b 1 0 Tc v) 87e-3 3`
2. `RoundsTo (acentric ps (cubicP R (A / √Tc) b 1 0 Tc v)) 58e-3 3`

Program definitions in this claim:

- `IsCriticalIsotherm p v` — **PINNED** (pin theorem `criticalSpec_pins`): phrase (hand-written, linted): the critical point condition of an isotherm holds for the isotherm pressure function of molar volume `p` at the molar volume at the point `v` (pressure as a function of molar volume at fixed temperature): its first and second derivatives vanish at `v`; by definition, means (`deriv p v = 0`) and (`deriv (deriv p) v = 0`)
- `IsMaxwellCoexistence p vl vg ps` — **PINNED** (pin theorem `maxwellSpec_pins`): phrase (hand-written, linted): the Maxwell equal area coexistence condition holds for the liquid molar volume `vl` and the gas molar volume `vg`, with `vl` below `vg`, on the isotherm pressure function of molar volume `p` at the saturation pressure `ps`: the isotherm takes the value `ps` at both, and its integral from `vl` to `vg` equals `ps` times the volume difference; by definition, means (`vl < vg`) and (`p vl = ps`) and (`p vg = ps`) and (`∫ (v : ℝ) in vl..vg, p v = ps * (vg - vl)`)
- `RoundsTo x d k` — MATH, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_RoundsTo`) (for `x : ℝ`, `d : ℝ`, `k : ℕ`): means `|x - d| ≤ 1 / (2 * 10 ^ k)`
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

## Your answers: use ANSWER_FORM.md, item 65
