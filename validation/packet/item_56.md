# Item 56

**Area:** Certified numbers of the findings

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Sec. XI, Eqs. (11.42)–(11.45) (p. 121), from Capozziello, Cardone, Salzano 2008 (arXiv:0802.1583) Eqs. (43)–(44) and the display after (44): the first-order deviations η₂₀ = F″(R₀)H₀⁴/F(R₀), η₃₀ = F‴(R₀)H₀⁶/F(R₀) of F(R) from GR are wrong, formulas and numbers

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**It holds that**

- there is `ε : ℝ` such that (`RoundsTo ε 32e-3 3`) and (`Jfam (41 / 1000) ε = 0`)

Program definitions in this claim:

- `Jfam Ω ε` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_Jfam`) (for `Ω : ℝ`, `ε : ℝ`): is defined as `jL * (1 + ε) - qL Ω * (1 + ε) - 2`
- `RoundsTo x d k` — MATH, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_RoundsTo`) (for `x : ℝ`, `d : ℝ`, `k : ℕ`): means `|x - d| ≤ 1 / (2 * 10 ^ k)`
- `jL` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_jL`); its name is not checked: is defined as `1`
- `qL Ω` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_qL`); its name is not checked (for `Ω : ℝ`): is defined as `3 / 2 * Ω - 1`

## Author's paraphrase (hand-written; checked only by prose rules)

At `Ω = 0.041` there is an `ε ≈ 0.032` at which the ε-family (11.41) reaches `j₀ − q₀ − 2 = 0`.

## Formal statement (Lean 4)

```lean
theorem F10_family_pole : ∃ ε : ℝ, RoundsTo ε 0.032 3 ∧ FREta.Jfam (41 / 1000) ε = 0 := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.FREta.jL`, `Cosmography.FREta.qL`, `Cosmography.FREta.Jfam`, `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): jL², qL².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): RoundsTo: d = 0.032, k = 3; Jfam: Ω = 41/1000.
- Source file: `Checked/Records/Findings.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 56
