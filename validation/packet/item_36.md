# Item 36

**Area:** Data claims

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**It holds that**

- there is `m : ℝ` such that (`IsGLB {x | ∃ H0 Ωm ΩΛ, Ωm ≤ 1 ∧ 0 ≤ ΩΛ ∧ (∀ (i : Fin 30), 0 ≤ e2OL Ωm ΩΛ (m16Table i).1) ∧ x = chiSqOL H0 Ωm ΩΛ} m`) and (`|m - 14.967| ≤ 5e-4`)

Program definitions in this claim:

- `chiSqOL H0 Ωm ΩΛ` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_chiSqOL`) (for `H0 : ℝ`, `Ωm : ℝ`, `ΩΛ : ℝ`): is defined as `∑ i, (H0 * √(e2OL Ωm ΩΛ (m16Table i).1) - (m16Table i).2.1) ^ 2 / (m16Table i).2.2 ^ 2 + (H0 - 73) ^ 2 / 2.4 ^ 2` ⚠ contains decimal constants that no check compares with a source
- `e2OL Ωm ΩΛ z` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_e2OL`) (for `Ωm : ℝ`, `ΩΛ : ℝ`, `z : ℝ`): is defined as `Ωm * (1 + z) ^ 3 + (1 - Ωm - ΩΛ) * (1 + z) ^ 2 + ΩΛ`
- `m16Table` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_m16Table`); its name is not checked: is defined as `![(7e-2, 69.0, 19.6), (9e-2, 69, 12), (0.12, 68.6, 26.2), (0.17, 83, 8), (0.179, 75, 4), (0.199, 75, 5), (0.20, 72.9, 29.6), (0.27, 77, 14), (0.28, 88.8, 36.6), (0.352, 83, 14), (0.3802, 83, 13.5), (0.4, 95, 17), (0.4004, 77, 10.2), (0.4247, 87.1, 11.2), (0.44497, 92.8, 12.9), (0.4783, 80.9, 9), (0.48, 97, 62), (0.593, 104, 13), (0.68, 92, 8), (0.781, 105, 12), (0.875, 125, 17), (0.88, 90, 40), (0.9, 117, 23), (1.037, 154, 20), (1.3, 168, 17), (1.363, 160, 33.6), (1.43, 177, 18), (1.53, 140, 14), (1.75, 202, 40), (1.965, 186.5, 50.4)]`

## Author's paraphrase (hand-written; checked only by prose rules)

The greatest lower bound of the χ² `chiSqOL` over the points (H₀, Ωm, ΩΛ) with Ωm ≤ 1,
ΩΛ ≥ 0 and E² nonnegative at the thirty z values of Table 4 exists and is within 0.0005 of 14.967.

## Formal statement (Lean 4)

```lean
theorem chiSqOL_glb_wide : ∃ m : ℝ,
    IsGLB {x | ∃ H0 Ωm ΩΛ : ℝ, Ωm ≤ 1 ∧ 0 ≤ ΩΛ ∧
      (∀ i, 0 ≤ e2OL Ωm ΩΛ (m16Table i).1) ∧ x = chiSqOL H0 Ωm ΩΛ} m ∧
    |m - 14.967| ≤ 0.0005 := …
```

## Definitions it uses

See GLOSSARY.md: `Data.Moresco16.m16Table`, `Data.Moresco16.chiSqOL`, `Data.Moresco16.e2OL`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): m16Table².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Data/Moresco16Min.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 36
