# Item 28

**Area:** F11

**Source:** Demianski, Piedipalumbo, Sawant, Amati, A&A 598, A113 (2017), arXiv:1609.09631 (v1, v2), p. 3: flat z-series D⁴_L has −105q₀⁴ (should be +105q₀⁴) and D⁴_A (Eq. (23)) has +137j₀ (should be −137j₀); the D⁴_L error is reprinted in Lusso et al., A&A 628, L4 (2019), arXiv:1907.07692 (v1–v4), the quasar+SN+GRB paper claiming > 4σ tension with flat ΛCDM

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`:

**then**

1. `correctDL4z q j s l 0 - demDL4 q j s l = 7 / 4 * q ^ 4`
2. `correctDA4z q j s l 0 - demDA4 q j s l = -(137 / 60) * j`

Program definitions in this claim:

- `correctDA4z q j s l k` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_correctDA4z`) (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`, `k : ℝ`): is defined as `printedDA4z q j s l k + k ^ 2 / 120`
- `correctDL4z q j s l k` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_correctDL4z`) (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`, `k : ℝ`): is defined as `printedDL4z q j s l k + k ^ 2 / 120`
- `demDA4 q j s l` — PRINTED, not pinned, so only the formula shown is checked, not its name (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`): is defined as `1 / 120 * (274 + 326 * q + 411 * q ^ 2 + 315 * q ^ 3 + 105 * q ^ 4 - 210 * q * j - 105 * q ^ 2 * j - 15 * q * s + 137 * j + 10 * j ^ 2 - 21 * s - l)`
- `demDL4 q j s l` — PRINTED, not pinned, so only the formula shown is checked, not its name (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`): is defined as `1 / 120 * (-6 + 6 * q + 81 * q ^ 2 + 165 * q ^ 3 - 105 * q ^ 4 - 110 * q * j + -105 * q ^ 2 * j - 15 * q * s - 27 * j + 10 * j ^ 2 - 11 * s - l)`
- `printedDA4z q j s l k` — PRINTED, not pinned, so only the formula shown is checked, not its name (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`, `k : ℝ`): is defined as `1 / 120 * (274 + 326 * q + 411 * q ^ 2 + 315 * q ^ 3 + 105 * q ^ 4 - 210 * q * j - 105 * q ^ 2 * j - 15 * q * s + -137 * j + 10 * j ^ 2 - 21 * s - l - 5 * k * (17 + 20 * q + 9 * q ^ 2 - 2 * j))`
- `printedDL4z q j s l k` — PRINTED, not pinned, so only the formula shown is checked, not its name (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`, `k : ℝ`): is defined as `1 / 120 * (-6 + 6 * q + 81 * q ^ 2 + 165 * q ^ 3 + 105 * q ^ 4 - 110 * q * j - 105 * q ^ 2 * j - 15 * q * s + -27 * j + 10 * j ^ 2 - 11 * s - l - 5 * k * (1 + 8 * q + 9 * q ^ 2 - 2 * j))`

## Author's paraphrase (hand-written; checked only by prose rules)

The printed coefficients against the correct flat ones: `D⁴_L` misses `+(7/4)q₀⁴`
(`−105q₀⁴` for `+105q₀⁴`), `D⁴_A` has `+(137/60)j₀` too much (`+137j₀` for `−137j₀`).

## Formal statement (Lean 4)

```lean
theorem flat_corrections (q j s l : ℝ) :
    correctDL4z q j s l 0 - demDL4 q j s l = 7 / 4 * q ^ 4 ∧
    correctDA4z q j s l 0 - demDA4 q j s l = -(137 / 60) * j := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.BambaZ.printedDA4z`, `Cosmography.BambaZ.printedDL4z`, `Cosmography.DemianskiZ.demDA4`, `Cosmography.DemianskiZ.demDL4`, `Cosmography.BambaZ.correctDA4z`, `Cosmography.BambaZ.correctDL4z`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): printedDA4z², printedDL4z², demDA4², demDL4².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): correctDL4z: k = 0; correctDA4z: k = 0.
- Source file: `Checked/Cosmography/DemianskiZ.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 28
