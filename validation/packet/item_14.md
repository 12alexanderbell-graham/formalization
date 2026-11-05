# Item 14

**Area:** F10

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Sec. XI, Eqs. (11.42)–(11.45) (p. 121), from Capozziello, Cardone, Salzano 2008 (arXiv:0802.1583) Eqs. (43)–(44) and the display after (44): the first-order deviations η₂₀ = F″(R₀)H₀⁴/F(R₀), η₃₀ = F‴(R₀)H₀⁶/F(R₀) of F(R) from GR are wrong, formulas and numbers

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `Ω : ℝ`:

**assuming**

1. `0 < Ω`
2. `Ω < 1`
3. `printedDen Ω ≠ 0`
4. `(54 * Ω ^ 2 - 29 * Ω - 2) * (27 * Ω ^ 2 + 24 * Ω - 32) ≠ 0`

**then**

- it is false that (`HasDerivAt (eta30 Ω) (printed30 Ω) 0`)

Program definitions in this claim:

- `P0 q j s l` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_P0`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`): is defined as `(j - q - 2) * l - (3 * s + 7 * j + 6 * q ^ 2 + 41 * q + 22) * s - ((3 * q + 16) * j + 20 * q ^ 2 + 64 * q + 12) * j - (3 * q ^ 4 + 25 * q ^ 3 + 96 * q ^ 2 + 72 * q + 20)`
- `P3 q j s l` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_P3`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`): is defined as `3 * l + 3 * s - 9 * (q + 4) * j - (45 * q ^ 2 + 78 * q + 12)`
- `Q0 q j s l` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_Q0`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`): is defined as `(q ^ 2 - j * q + 2 * q) * l + (3 * q * s + (4 * q + 6) * j + 6 * q ^ 3 + 44 * q ^ 2 + 22 * q - 12) * s + (2 * j ^ 2 + (3 * q ^ 2 + 10 * q - 6) * j + 17 * q ^ 3 + 52 * q ^ 2 + 54 * q + 36) * j + (3 * q ^ 5 + 28 * q ^ 4 + 118 * q ^ 3 + 72 * q ^ 2 - 76 * q - 64)`
- `Q3 q j s l` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_Q3`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`): is defined as `-(2 * (1 + q) * l + 2 * (j + q) * s - (2 * j + 4 * q ^ 2 + 12 * q + 6) * j - (30 * q ^ 3 + 84 * q ^ 2 + 78 * q + 24))`
- `eta30 Ω ε` — COMPOSITE, not pinned, so only the formula shown is checked, not its name (for `Ω : ℝ`, `ε : ℝ`): is defined as `eta30Of Ω (qL Ω * (1 + ε)) (jL * (1 + ε)) (sL Ω * (1 + ε)) (lL Ω * (1 + ε))`
- `eta30Of Ω q j s l` — FORMULA, not pinned, so only the formula shown is checked, not its name (for `Ω : ℝ`, `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`): is defined as `(P3 q j s l * Ω + Q3 q j s l) / (216 * (j - q - 2) * (P0 q j s l * Ω + Q0 q j s l))`
- `jL` — PRINTED, not pinned, so only the formula shown is checked, not its name: is defined as `1`
- `lL Ω` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_lL`); its name is not checked (for `Ω : ℝ`): is defined as `1 + 3 * Ω + 27 / 2 * Ω ^ 2`
- `printed30 Ω` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_printed30`); its name is not checked (for `Ω : ℝ`): is defined as `(6 * ((81 * Ω - 110) * Ω + 40) * Ω + 16) / printedDen Ω * (1 / (243 * Ω ^ 2))`
- `printedDen Ω` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_printedDen`); its name is not checked (for `Ω : ℝ`): is defined as `(3 * (9 * Ω + 74) * Ω - 556) * Ω ^ 2 + 16`
- `qL Ω` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_qL`); its name is not checked (for `Ω : ℝ`): is defined as `3 / 2 * Ω - 1`
- `sL Ω` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_sL`); its name is not checked (for `Ω : ℝ`): is defined as `1 - 9 / 2 * Ω`

## Author's paraphrase (hand-written; checked only by prose rules)

Printed (11.43) fails at the same parameter values.

## Formal statement (Lean 4)

```lean
theorem printedEta30_false_at {Ω : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1) (hd : printedDen Ω ≠ 0)
    (hne : (54 * Ω ^ 2 - 29 * Ω - 2) * (27 * Ω ^ 2 + 24 * Ω - 32) ≠ 0) :
    ¬ HasDerivAt (eta30 Ω) (printed30 Ω) 0 := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.FRCosmo.P0`, `Cosmography.FRCosmo.P3`, `Cosmography.FRCosmo.Q0`, `Cosmography.FRCosmo.Q3`, `Cosmography.FREta.jL`, `Cosmography.FREta.lL`, `Cosmography.FREta.printed30`, `Cosmography.FREta.printedDen`, `Cosmography.FREta.qL`, `Cosmography.FREta.sL`, `Cosmography.FREta.eta30`, `Cosmography.FREta.eta30Of`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): P0², P3², Q0², Q3², jL, lL², printed30², printedDen², qL², sL².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `printedEta30_false_at`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Cosmography/FREta.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 14
