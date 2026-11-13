# Item 14

**Area:** Certified numbers of the findings

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Sec. XI, Eqs. (11.42)–(11.45) (p. 121), from Capozziello, Cardone, Salzano 2008 (arXiv:0802.1583) Eqs. (43)–(44) and the display after (44): the first-order deviations η₂₀ = F″(R₀)H₀⁴/F(R₀), η₃₀ = F‴(R₀)H₀⁶/F(R₀) of F(R) from GR are wrong, formulas and numbers

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**It holds that**

- there is `r : ℝ` such that (`RoundsTo r 0.176 3`) and (`printedDen r = 0`)

Program definitions in this claim:

- `RoundsTo x d k` — MATH, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_RoundsTo`) (for `x : ℝ`, `d : ℝ`, `k : ℕ`): means `|x - d| ≤ 1 / (2 * 10 ^ k)`
- `printedDen Ω` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_printedDen`); its name is not checked (for `Ω : ℝ`): is defined as `(3 * (9 * Ω + 74) * Ω - 556) * Ω ^ 2 + 16`

## Author's paraphrase (hand-written; checked only by prose rules)

The printed denominator (11.42)–(11.43) vanishes at some `Ω ≈ 0.176` (spurious pole).

## Formal statement (Lean 4)

```lean
theorem F10_printed_pole : ∃ r : ℝ, RoundsTo r 0.176 3 ∧ FREta.printedDen r = 0 := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.FREta.printedDen`, `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): printedDen².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): RoundsTo: d = 0.176, k = 3.
- Source file: `Checked/Records/Findings.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 14
