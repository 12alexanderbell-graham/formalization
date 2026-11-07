# Item 50

**Area:** F8

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Eqs. (10.38)–(10.51), verbatim from Capozziello & Salzano 2009 (arXiv:0902.0088) Eqs. (31)–(52): z-redshift d_L and d_A fourth-order coefficients D⁴_L, D⁴_A miss the curvature-squared term

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`:

**then**

1. `printedDL4z q j s l 0 = correctDL4z q j s l 0`
2. `printedDA4z q j s l 0 = correctDA4z q j s l 0`

Program definitions in this claim:

- `correctDA4z q j s l k` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_correctDA4z`) (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`, `k : ℝ`): is defined as `printedDA4z q j s l k + k ^ 2 / 120`
- `correctDL4z q j s l k` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_correctDL4z`) (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`, `k : ℝ`): is defined as `printedDL4z q j s l k + k ^ 2 / 120`
- `printedDA4z q j s l k` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_printedDA4z`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`, `k : ℝ`): is defined as `1 / 120 * (274 + 326 * q + 411 * q ^ 2 + 315 * q ^ 3 + 105 * q ^ 4 - 210 * q * j - 105 * q ^ 2 * j - 15 * q * s + -137 * j + 10 * j ^ 2 - 21 * s - l - 5 * k * (17 + 20 * q + 9 * q ^ 2 - 2 * j))`
- `printedDL4z q j s l k` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_printedDL4z`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`, `k : ℝ`): is defined as `1 / 120 * (-6 + 6 * q + 81 * q ^ 2 + 165 * q ^ 3 + 105 * q ^ 4 - 110 * q * j - 105 * q ^ 2 * j - 15 * q * s + -27 * j + 10 * j ^ 2 - 11 * s - l - 5 * k * (1 + 8 * q + 9 * q ^ 2 - 2 * j))`

## Author's paraphrase (hand-written; checked only by prose rules)

The flat parts are right: at `K = 0` the corrections vanish.

## Formal statement (Lean 4)

```lean
theorem printed_flat_eq (q j s l : ℝ) :
    printedDL4z q j s l 0 = correctDL4z q j s l 0 ∧ printedDA4z q j s l 0 = correctDA4z q j s l 0 := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.BambaZ.printedDA4z`, `Cosmography.BambaZ.printedDL4z`, `Cosmography.BambaZ.correctDA4z`, `Cosmography.BambaZ.correctDL4z`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): printedDA4z², printedDL4z².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): printedDL4z: k = 0; correctDL4z: k = 0; printedDA4z: k = 0; correctDA4z: k = 0.
- Source file: `Checked/Cosmography/BambaZ.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 50
