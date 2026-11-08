# Item 49

**Area:** F10

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Sec. XI, Eqs. (11.42)–(11.45) (p. 121), from Capozziello, Cardone, Salzano 2008 (arXiv:0802.1583) Eqs. (43)–(44) and the display after (44): the first-order deviations η₂₀ = F″(R₀)H₀⁴/F(R₀), η₃₀ = F‴(R₀)H₀⁶/F(R₀) of F(R) from GR are wrong, formulas and numbers

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**It holds that**

- it is false that (`PrintedEta20Claim`)

Program definitions in this claim:

- `P0 q j s l` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_P0`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`): is defined as `(j - q - 2) * l - (3 * s + 7 * j + 6 * q ^ 2 + 41 * q + 22) * s - ((3 * q + 16) * j + 20 * q ^ 2 + 64 * q + 12) * j - (3 * q ^ 4 + 25 * q ^ 3 + 96 * q ^ 2 + 72 * q + 20)`
- `P2 q j s` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_P2`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`): is defined as `9 * s + 6 * j + 9 * q ^ 2 + 66 * q + 42`
- `PrintedEta20Claim` — CLAIM, not pinned, so only the formula shown is checked, not its name: means for every `Ω : ℝ`, if `0 < Ω`, then if `Ω < 1`, then if `printedDen Ω ≠ 0`, then `HasDerivAt (eta20 Ω) (printed20 Ω) 0`
- `Q0 q j s l` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_Q0`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`): is defined as `(q ^ 2 - j * q + 2 * q) * l + (3 * q * s + (4 * q + 6) * j + 6 * q ^ 3 + 44 * q ^ 2 + 22 * q - 12) * s + (2 * j ^ 2 + (3 * q ^ 2 + 10 * q - 6) * j + 17 * q ^ 3 + 52 * q ^ 2 + 54 * q + 36) * j + (3 * q ^ 5 + 28 * q ^ 4 + 118 * q ^ 3 + 72 * q ^ 2 - 76 * q - 64)`
- `Q2 q j s` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_Q2`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`): is defined as `-(6 * (q + 1) * s + (2 * j - 2 * (1 - q)) * j + 6 * q ^ 3 + 50 * q ^ 2 + 74 * q + 32)`
- `eta20 Ω ε` — COMPOSITE, not pinned, so only the formula shown is checked, not its name (for `Ω : ℝ`, `ε : ℝ`): is defined as `eta20Of Ω (qL Ω * (1 + ε)) (jL * (1 + ε)) (sL Ω * (1 + ε)) (lL Ω * (1 + ε))`
- `eta20Of Ω q j s l` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_eta20Of`) (for `Ω : ℝ`, `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`): is defined as `(P2 q j s * Ω + Q2 q j s) / (36 * (P0 q j s l * Ω + Q0 q j s l))`
- `jL` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_jL`); its name is not checked: is defined as `1`
- `lL Ω` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_lL`); its name is not checked (for `Ω : ℝ`): is defined as `1 + 3 * Ω + 27 / 2 * Ω ^ 2`
- `printed20 Ω` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_printed20`); its name is not checked (for `Ω : ℝ`): is defined as `(64 - 6 * Ω * (9 * Ω + 8)) / printedDen Ω * (1 / 27)`
- `printedDen Ω` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_printedDen`); its name is not checked (for `Ω : ℝ`): is defined as `(3 * (9 * Ω + 74) * Ω - 556) * Ω ^ 2 + 16`
- `qL Ω` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_qL`); its name is not checked (for `Ω : ℝ`): is defined as `3 / 2 * Ω - 1`
- `sL Ω` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_sL`); its name is not checked (for `Ω : ℝ`): is defined as `1 - 9 / 2 * Ω`

## Author's paraphrase (hand-written; checked only by prose rules)

The review's (11.42), read as the first-order statement `η₂₀(Ω, ε) = η₂₀(Ω, 0) + printed20(Ω)·ε + o(ε)`
(derivative in `ε` at `0` on the family (11.41)) for every `0 < Ω < 1` where the printed denominator is
nonzero, is false.

## Formal statement (Lean 4)

```lean
theorem printedEta20Claim_false : ¬ PrintedEta20Claim := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.FRCosmo.P0`, `Cosmography.FRCosmo.P2`, `Cosmography.FRCosmo.Q0`, `Cosmography.FRCosmo.Q2`, `Cosmography.FREta.PrintedEta20Claim`, `Cosmography.FREta.jL`, `Cosmography.FREta.lL`, `Cosmography.FREta.printed20`, `Cosmography.FREta.printedDen`, `Cosmography.FREta.qL`, `Cosmography.FREta.sL`, `Cosmography.FREta.eta20`, `Cosmography.FREta.eta20Of`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): P0², P2², Q0², Q2², PrintedEta20Claim, jL², lL², printed20², printedDen², qL², sL².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Cosmography/FREta.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 49
