# Item 21

**Area:** Chemistry

**Source:** generalized two-parameter cubic equation of state: van der Waals (1873), Redlich & Kwong, Chem. Rev. 44, 233 (1949), Soave, Chem. Eng. Sci. 27, 1197 (1972), Peng & Robinson, Ind. Eng. Chem. Fundam. 15, 59 (1976)

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `R : ℝ`, `a : ℝ`, `b : ℝ`:

**assuming**

1. `0 < R`
2. `0 < a`
3. `0 < b`

**then**

- there is `vl : ℝ` such that there is `vg : ℝ` such that there is `ps : ℝ` such that (`b < vl`) and (the Maxwell equal area coexistence condition holds for the liquid molar volume `vl` and the gas molar volume `vg`, with `vl` below `vg`, on the isotherm pressure function of molar volume `p := cubicP R a b 0 0 (7 / 10 * (8 * a / (27 * R * b)))` at the saturation pressure `ps`: the isotherm takes the value `ps` at both, and its integral from `vl` to `vg` equals `ps` times the volume difference) and (`RoundsTo (ps / (a / (27 * b ^ 2))) 0.20046 5`) and (`RoundsTo (acentric ps (a / (27 * b ^ 2))) (-0.3020) 4`)

Program definitions in this claim:

- `IsMaxwellCoexistence p vl vg ps` — **PINNED** (pin theorem `maxwellSpec_pins`): phrase (hand-written, linted): the Maxwell equal area coexistence condition holds for the liquid molar volume `vl` and the gas molar volume `vg`, with `vl` below `vg`, on the isotherm pressure function of molar volume `p` at the saturation pressure `ps`: the isotherm takes the value `ps` at both, and its integral from `vl` to `vg` equals `ps` times the volume difference; by definition, means (`vl < vg`) and (`p vl = ps`) and (`p vg = ps`) and (`∫ (v : ℝ) in vl..vg, p v = ps * (vg - vl)`)
- `RoundsTo x d k` — MATH, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_RoundsTo`) (for `x : ℝ`, `d : ℝ`, `k : ℕ`): means `|x - d| ≤ 1 / (2 * 10 ^ k)`
- `acentric ps pc` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_acentric`) (for `ps : ℝ`, `pc : ℝ`): is defined as `-Real.logb 10 (ps / pc) - 1`
- `cubicP R a b u w T v` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_cubicP`) (for `R : ℝ`, `a : ℝ`, `b : ℝ`, `u : ℝ`, `w : ℝ`, `T : ℝ`, `v : ℝ`): is defined as `R * T / (v - b) - a / (v ^ 2 + u * b * v + w * b ^ 2)`

## Author's paraphrase (hand-written; checked only by prose rules)

van der Waals fluid at T = 0.7 · 8a/(27Rb) (that is 0.7 T_c): there is a Maxwell coexistence
state (liquid volume above the co-volume b), and its pressure is 0.20046 · a/(27b²) (that is
0.20046 P_c) to five decimals, so the acentric factor of the van der Waals fluid is −0.3020 to four
decimals.

## Formal statement (Lean 4)

```lean
theorem vdW_coexistence_exists (R a b : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    ∃ vl vg ps, b < vl ∧
      IsMaxwellCoexistence (cubicP R a b 0 0 (7 / 10 * (8 * a / (27 * R * b)))) vl vg ps ∧
      RoundsTo (ps / (a / (27 * b ^ 2))) 0.20046 5 ∧
      RoundsTo (acentric ps (a / (27 * b ^ 2))) (-0.3020) 4 := …
```

## Definitions it uses

See GLOSSARY.md: `Chemistry.Coexistence.IsMaxwellCoexistence`, `Chemistry.Coexistence.acentric`, `Chemistry.CubicEOS.cubicP`, `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsMaxwellCoexistence.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `vdW_coexistence_exists`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cubicP: u = 0, w = 0; RoundsTo: d = 0.20046, k = 5, d = -0.3020, k = 4.
- Source file: `Checked/Chemistry/Coexistence.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 21
