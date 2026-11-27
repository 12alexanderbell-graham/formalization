# Item 38

**Area:** Data claims

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** the statement is proved in module `Checked.Data.Moresco16Min` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source), in two parts. (A) Re-derived by the kernel from the statement; holds whoever wrote the statement, its witnesses and its proofs; shows the statement is not vacuous and which hypotheses matter, not that it says what its source says:** non-vacuity: nothing to witness (the statement has no hypothesis to meet); hypotheses: none numbered; no assumption outside the numbering (`TRUST_MAP.md`, shape); part A complete. **(B) Rests on who wrote a statement; CI checks the route of each item (commit order, briefs without the answer), not that its writer was independent of the authors, so each item is evidence of meaning only as far as that independence holds:** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; statement literals: no blind second reading registered; 4 literals of the statement are grandfathered as never read twice (`scripts/trust/literal_baseline.txt`); program definitions the claim uses (listed under the claim): 0 pinned by a specification the program wrote (the kernel checks that the specification determines the definition, not that it says what the source means), 0 of them also determined by a blind reader's specification that they meet (on the domain printed with the definition), 3 with a blind second reading or formulation, 0 with neither (only the formula printed is checked). The statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**It holds that**

- there is `H0 : ℝ` such that there is `Ωm : ℝ` such that there is `ΩΛ : ℝ` such that (`0 ≤ Ωm`) and (`Ωm ≤ 1`) and (`Ωm ≤ 2 * ΩΛ`) and (`2 * ΩΛ ≤ 15.625 * Ωm`) and (for every `i : Fin 30`, `0 < e2OL Ωm ΩΛ (m16Table i).1`) and (`chiSqOL H0 Ωm ΩΛ < 14.9675`)

Program definitions in this claim:

- `chiSqOL H0 Ωm ΩΛ` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_chiSqOL`) (for `H0 : ℝ`, `Ωm : ℝ`, `ΩΛ : ℝ`): is defined as `∑ i, (H0 * √(e2OL Ωm ΩΛ (m16Table i).1) - (m16Table i).2.1) ^ 2 / (m16Table i).2.2 ^ 2 + (H0 - 73) ^ 2 / 2.4 ^ 2` ⚠ contains decimal constants that no check compares with a source
- `e2OL Ωm ΩΛ z` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_e2OL`) (for `Ωm : ℝ`, `ΩΛ : ℝ`, `z : ℝ`): is defined as `Ωm * (1 + z) ^ 3 + (1 - Ωm - ΩΛ) * (1 + z) ^ 2 + ΩΛ`
- `m16Table` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_m16Table`); its name is not checked: is defined as `![(7e-2, 69.0, 19.6), (9e-2, 69, 12), (0.12, 68.6, 26.2), (0.17, 83, 8), (0.179, 75, 4), (0.199, 75, 5), (0.20, 72.9, 29.6), (0.27, 77, 14), (0.28, 88.8, 36.6), (0.352, 83, 14), (0.3802, 83, 13.5), (0.4, 95, 17), (0.4004, 77, 10.2), (0.4247, 87.1, 11.2), (0.44497, 92.8, 12.9), (0.4783, 80.9, 9), (0.48, 97, 62), (0.593, 104, 13), (0.68, 92, 8), (0.781, 105, 12), (0.875, 125, 17), (0.88, 90, 40), (0.9, 117, 23), (1.037, 154, 20), (1.3, 168, 17), (1.363, 160, 33.6), (1.43, 177, 18), (1.53, 140, 14), (1.75, 202, 40), (1.965, 186.5, 50.4)]`

## Author's paraphrase (hand-written; checked only by prose rules)

There are H₀, Ω_m, Ω_Λ in the paper's prior region (0 ≤ Ω_m ≤ 1 and 1 ≤ 2Ω_Λ/Ω_m ≤ 15.625)
with E² positive at the thirty z values of Table 4, at which the χ² `chiSqOL` is below 14.9675.

## Formal statement (Lean 4)

```lean
theorem chiSqOL_lt : ∃ H0 Ωm ΩΛ : ℝ, 0 ≤ Ωm ∧ Ωm ≤ 1 ∧ Ωm ≤ 2 * ΩΛ ∧
    2 * ΩΛ ≤ 15.625 * Ωm ∧ (∀ i, 0 < e2OL Ωm ΩΛ (m16Table i).1) ∧
    chiSqOL H0 Ωm ΩΛ < 14.9675 := …
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

## Your answers: use ANSWER_FORM.md, item 38
