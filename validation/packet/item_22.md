# Item 22

**Area:** Chemistry

**Source:** generalized two-parameter cubic equation of state: van der Waals (1873), Redlich & Kwong, Chem. Rev. 44, 233 (1949), Soave, Chem. Eng. Sci. 27, 1197 (1972), Peng & Robinson, Ind. Eng. Chem. Fundam. 15, 59 (1976)

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `R : ℝ`, `a : ℝ`, `b : ℝ`, `vl : ℝ`, `vg : ℝ`, `ps : ℝ`:

**assuming**

1. `0 < R`
2. `0 < a`
3. `0 < b`
4. `b < vl`
5. the molar volumes `vl` < `vg` are in Maxwell coexistence on the isotherm `cubicP R a b 0 0 (7 / 10 * (8 * a / (27 * R * b)))` at pressure `ps`: p(`vl`) = p(`vg`) = `ps` and the integral of p from `vl` to `vg` equals `ps`·(`vg` − `vl`)

**then**

- `RoundsTo (ps / (a / (27 * b ^ 2))) 0.20046 5`

Program definitions in this claim:

- `IsMaxwellCoexistence p vl vg ps` — **PINNED** (pin theorem `maxwellSpec_pins`): the molar volumes `vl` < `vg` are in Maxwell coexistence on the isotherm `p` at pressure `ps`: p(`vl`) = p(`vg`) = `ps` and the integral of p from `vl` to `vg` equals `ps`·(`vg` − `vl`)
- `RoundsTo x d k` — MATH, not pinned, so only the formula shown is checked, not its name (for `x : ℝ`, `d : ℝ`, `k : ℕ`): means `|x - d| ≤ 1 / (2 * 10 ^ k)`
- `cubicP R a b u w T v` — FORMULA, not pinned, so only the formula shown is checked, not its name (for `R : ℝ`, `a : ℝ`, `b : ℝ`, `u : ℝ`, `w : ℝ`, `T : ℝ`, `v : ℝ`): is defined as `R * T / (v - b) - a / (v ^ 2 + u * b * v + w * b ^ 2)`

## Author's paraphrase (hand-written; checked only by prose rules)

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
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cubicP: u = 0, w = 0; RoundsTo: d = 0.20046, k = 5.
- Source file: `Checked/Chemistry/Coexistence.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 22
