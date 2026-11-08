# Item 38

**Area:** Chemistry

**Source:** generalized two-parameter cubic equation of state: van der Waals (1873), Redlich & Kwong, Chem. Rev. 44, 233 (1949), Soave, Chem. Eng. Sci. 27, 1197 (1972), Peng & Robinson, Ind. Eng. Chem. Fundam. 15, 59 (1976)

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `R : ℝ`, `ac : ℝ`, `b : ℝ`, `Tc : ℝ`, `v : ℝ` (renamed by the generator after the pinned slot it fills; the statement calls it `vc`):

**assuming**

1. `0 < ac`
2. `0 < b`
3. `b < v`
4. the molar volume `v` is a critical point of the isotherm `p := cubicP R ac b 1 0 Tc` (pressure as a function of molar volume at fixed temperature): its first and second derivatives vanish at `v`

**then**

- there is `vl : ℝ` such that there is `vg : ℝ` such that there is `ps : ℝ` such that (`b < vl`) and (the molar volumes `vl` and `vg`, with `vl` below `vg`, are in Maxwell coexistence on the isotherm `p := cubicP R (ac * (1 + (0.480 + 1.574 * 1 - 0.176 * 1 ^ 2) * (1 - √(7 / 10))) ^ 2) b 1 0 (7 / 10 * Tc)` at the pressure `ps`: the isotherm takes the value `ps` at both, and its integral from `vl` to `vg` equals `ps` times the volume difference) and (`RoundsTo (ps / cubicP R ac b 1 0 Tc v) 102e-4 4`) and (`RoundsTo (acentric ps (cubicP R ac b 1 0 Tc v)) 0.992 3`)

Program definitions in this claim:

- `IsCriticalIsotherm p v` — **PINNED** (pin theorem `criticalSpec_pins`): phrase (hand-written, linted): the molar volume `v` is a critical point of the isotherm `p` (pressure as a function of molar volume at fixed temperature): its first and second derivatives vanish at `v`; by definition, means (`deriv p v = 0`) and (`deriv (deriv p) v = 0`)
- `IsMaxwellCoexistence p vl vg ps` — **PINNED** (pin theorem `maxwellSpec_pins`): phrase (hand-written, linted): the molar volumes `vl` and `vg`, with `vl` below `vg`, are in Maxwell coexistence on the isotherm `p` at the pressure `ps`: the isotherm takes the value `ps` at both, and its integral from `vl` to `vg` equals `ps` times the volume difference; by definition, means (`vl < vg`) and (`p vl = ps`) and (`p vg = ps`) and (`∫ (v : ℝ) in vl..vg, p v = ps * (vg - vl)`)
- `RoundsTo x d k` — MATH, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_RoundsTo`) (for `x : ℝ`, `d : ℝ`, `k : ℕ`): means `|x - d| ≤ 1 / (2 * 10 ^ k)`
- `acentric ps pc` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_acentric`) (for `ps : ℝ`, `pc : ℝ`): is defined as `-Real.logb 10 (ps / pc) - 1`
- `cubicP R a b u w T v` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_cubicP`) (for `R : ℝ`, `a : ℝ`, `b : ℝ`, `u : ℝ`, `w : ℝ`, `T : ℝ`, `v : ℝ`): is defined as `R * T / (v - b) - a / (v ^ 2 + u * b * v + w * b ^ 2)`

## Author's paraphrase (hand-written; checked only by prose rules)

Soave–Redlich–Kwong fluid with Soave's κ(ω) correlation at ω = 1: at any critical point (v_c > b)
there is a Maxwell coexistence state at T = 0.7 T_c with liquid volume above the co-volume b, and
its pressure is 0.0102 times the critical pressure (4 decimals) and its acentric factor 0.992
(3 decimals).

## Formal statement (Lean 4)

```lean
theorem srk_omega1_exists (R ac b Tc vc : ℝ) (hac : 0 < ac) (hb : 0 < b) (hvc : b < vc)
    (hc : IsCriticalIsotherm (cubicP R ac b 1 0 Tc) vc) :
    ∃ vl vg ps, b < vl ∧
      IsMaxwellCoexistence
        (cubicP R (ac * (1 + (0.480 + 1.574 * 1 - 0.176 * 1 ^ 2) *
          (1 - Real.sqrt (7 / 10))) ^ 2) b 1 0 (7 / 10 * Tc)) vl vg ps ∧
      RoundsTo (ps / cubicP R ac b 1 0 Tc vc) 0.0102 4 ∧
      RoundsTo (acentric ps (cubicP R ac b 1 0 Tc vc)) 0.992 3 := …
```

## Definitions it uses

See GLOSSARY.md: `Chemistry.Coexistence.IsMaxwellCoexistence`, `Chemistry.CubicEOS.IsCriticalIsotherm`, `Chemistry.Coexistence.acentric`, `Chemistry.CubicEOS.cubicP`, `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsMaxwellCoexistence, IsCriticalIsotherm.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `srk_omega1_exists`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cubicP: u = 1, w = 0; RoundsTo: d = 0.0102, k = 4, d = 0.992, k = 3.
- Source file: `Checked/Chemistry/SRKAcentric.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 38
