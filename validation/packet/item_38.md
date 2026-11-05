# Item 38

**Area:** Chemistry

**Source:** generalized two-parameter cubic equation of state: van der Waals (1873), Redlich & Kwong, Chem. Rev. 44, 233 (1949), Soave, Chem. Eng. Sci. 27, 1197 (1972), Peng & Robinson, Ind. Eng. Chem. Fundam. 15, 59 (1976)

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `R : ℝ`, `ac : ℝ`, `b : ℝ`, `Tc : ℝ`, `vc : ℝ`, `vl : ℝ`, `vg : ℝ`, `ps : ℝ`:

**assuming**

1. `0 < ac`
2. `0 < b`
3. `b < vc`
4. the molar volume `vc` is a critical point of the isotherm `cubicP R ac b 2 (-1) Tc` (pressure as a function of molar volume at fixed temperature): p′(`vc`) = 0 and p″(`vc`) = 0
5. `b < vl`
6. the molar volumes `vl` < `vg` are in Maxwell coexistence on the isotherm `cubicP R (ac * (1 + (0.37464 + 1.54226 * 1 - 0.26992 * 1 ^ 2) * (1 - √(7 / 10))) ^ 2) b 2 (-1) (7 / 10 * Tc)` at pressure `ps`: p(`vl`) = p(`vg`) = `ps` and the integral of p from `vl` to `vg` equals `ps`·(`vg` − `vl`)

**then**

1. `RoundsTo (ps / cubicP R ac b 2 (-1) Tc vc) 114e-4 4`
2. `RoundsTo (acentric ps (cubicP R ac b 2 (-1) Tc vc)) 0.942 3`

Program definitions in this claim:

- `IsCriticalIsotherm p v` — **PINNED** (pin theorem `criticalSpec_pins`): the molar volume `v` is a critical point of the isotherm `p` (pressure as a function of molar volume at fixed temperature): p′(`v`) = 0 and p″(`v`) = 0
- `IsMaxwellCoexistence p vl vg ps` — **PINNED** (pin theorem `maxwellSpec_pins`): the molar volumes `vl` < `vg` are in Maxwell coexistence on the isotherm `p` at pressure `ps`: p(`vl`) = p(`vg`) = `ps` and the integral of p from `vl` to `vg` equals `ps`·(`vg` − `vl`)
- `RoundsTo x d k` — MATH, not pinned, so only the formula shown is checked, not its name (for `x : ℝ`, `d : ℝ`, `k : ℕ`): means `|x - d| ≤ 1 / (2 * 10 ^ k)`
- `acentric ps pc` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_acentric`) (for `ps : ℝ`, `pc : ℝ`): is defined as `-Real.logb 10 (ps / pc) - 1`
- `cubicP R a b u w T v` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_cubicP`) (for `R : ℝ`, `a : ℝ`, `b : ℝ`, `u : ℝ`, `w : ℝ`, `T : ℝ`, `v : ℝ`): is defined as `R * T / (v - b) - a / (v ^ 2 + u * b * v + w * b ^ 2)`

## Author's paraphrase (hand-written; checked only by prose rules)

Peng–Robinson fluid with Soave's temperature function and the published κ(ω) at ω = 1
(attraction a_c at T_c, a_c (1 + κ(1)(1 − √0.7))² at 0.7 T_c): at any critical point
(v_c > b), every Maxwell coexistence state at T = 0.7 T_c with liquid volume above the co-volume
b has pressure 0.0114 times the critical pressure (4 decimals) and acentric factor 0.942
(3 decimals), not the input value 1.

## Formal statement (Lean 4)

```lean
theorem pr_omega1_unique (R ac b Tc vc vl vg ps : ℝ) (hac : 0 < ac) (hb : 0 < b)
    (hvc : b < vc)
    (hc : IsCriticalIsotherm (cubicP R ac b 2 (-1) Tc) vc)
    (hl : b < vl)
    (h : IsMaxwellCoexistence
      (cubicP R (ac * (1 + (0.37464 + 1.54226 * 1 - 0.26992 * 1 ^ 2) * (1 - Real.sqrt (7 / 10))) ^ 2)
        b 2 (-1) (7 / 10 * Tc)) vl vg ps) :
    RoundsTo (ps / cubicP R ac b 2 (-1) Tc vc) 0.0114 4 ∧
      RoundsTo (acentric ps (cubicP R ac b 2 (-1) Tc vc)) 0.942 3 := …
```

## Definitions it uses

See GLOSSARY.md: `Chemistry.Coexistence.IsMaxwellCoexistence`, `Chemistry.CubicEOS.IsCriticalIsotherm`, `Chemistry.Coexistence.acentric`, `Chemistry.CubicEOS.cubicP`, `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsMaxwellCoexistence, IsCriticalIsotherm.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `pr_omega1_unique`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cubicP: u = 2, w = -1; RoundsTo: d = 0.0114, k = 4, d = 0.942, k = 3.
- Source file: `Checked/Chemistry/PRAcentric.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 38
