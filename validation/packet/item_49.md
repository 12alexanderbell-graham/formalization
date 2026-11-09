# Item 49

**Area:** Chemistry

**Source:** generalized two-parameter cubic equation of state: van der Waals (1873), Redlich & Kwong, Chem. Rev. 44, 233 (1949), Soave, Chem. Eng. Sci. 27, 1197 (1972), Peng & Robinson, Ind. Eng. Chem. Fundam. 15, 59 (1976)

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `R : ℝ`, `a : ℝ`, `b : ℝ`, `u : ℝ`, `w : ℝ`:

**assuming**

1. `0 < R`
2. `0 < a`
3. `0 < b`
4. `-2 < u`
5. `0 < 1 + u + w`

**then**

- there is exactly one `p : ℝ × ℝ` such that (`0 < p.1`) and (`b < p.2`) and (the isotherm pressure function of molar volume `p := cubicP R a b u w p.1` satisfies the critical point condition of an isotherm with the molar volume at the point `v := p.2` (pressure as a function of molar volume at fixed temperature; first and second volume derivatives of pressure both vanish; a mere stationary point is not critical))

Program definitions in this claim:

- `IsCriticalIsotherm p v` — **PINNED** (pin theorem `criticalSpec_pins`): phrase (hand-written, linted): the isotherm pressure function of molar volume `p` satisfies the critical point condition of an isotherm with the molar volume at the point `v` (pressure as a function of molar volume at fixed temperature; first and second volume derivatives of pressure both vanish; a mere stationary point is not critical); by definition, means (`deriv p v = 0`) and (`deriv (deriv p) v = 0`)
- `cubicP R a b u w T v` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_cubicP`) (for `R : ℝ`, `a : ℝ`, `b : ℝ`, `u : ℝ`, `w : ℝ`, `T : ℝ`, `v : ℝ`): is defined as `R * T / (v - b) - a / (v ^ 2 + u * b * v + w * b ^ 2)`

## Author's paraphrase (hand-written; checked only by prose rules)

Existence and uniqueness of the critical point (T, v) of the generalized cubic EOS.

## Formal statement (Lean 4)

```lean
theorem exists_unique_critical (R a b u w : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)
    (hu : -2 < u) (h1 : 0 < 1 + u + w) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ b < p.2 ∧ IsCriticalIsotherm (cubicP R a b u w p.1) p.2 := …
```

## Definitions it uses

See GLOSSARY.md: `Chemistry.CubicEOS.IsCriticalIsotherm`, `Chemistry.CubicEOS.cubicP`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsCriticalIsotherm.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `exists_unique_critical`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Chemistry/CubicEOS.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 49
