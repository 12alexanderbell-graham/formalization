# Item 15

**Area:** F10

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Sec. XI, Eqs. (11.42)–(11.45) (p. 121), from Capozziello, Cardone, Salzano 2008 (arXiv:0802.1583) Eqs. (43)–(44) and the display after (44): the first-order deviations η₂₀ = F″(R₀)H₀⁴/F(R₀), η₃₀ = F‴(R₀)H₀⁶/F(R₀) of F(R) from GR are wrong, formulas and numbers

## Claim in plain words (the system's own text)

The review's (11.43), read as the first-order statement `η₃₀(Ω, ε) = η₃₀(Ω, 0) + printed30(Ω)·ε + o(ε)`
(derivative in `ε` at `0` on the family (11.41)) for every `0 < Ω < 1` where the printed denominator is
nonzero, is false.

## Formal statement (Lean 4)

```lean
theorem printedEta30Claim_false : ¬ PrintedEta30Claim := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.FRCosmo.P0`, `Cosmography.FRCosmo.P3`, `Cosmography.FRCosmo.Q0`, `Cosmography.FRCosmo.Q3`, `Cosmography.FREta.PrintedEta30Claim`, `Cosmography.FREta.jL`, `Cosmography.FREta.lL`, `Cosmography.FREta.printed30`, `Cosmography.FREta.printedDen`, `Cosmography.FREta.qL`, `Cosmography.FREta.sL`, `Cosmography.FREta.eta30`, `Cosmography.FREta.eta30Of`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): P0², P3², Q0², Q3², PrintedEta30Claim, jL, lL², printed30², printedDen², qL², sL².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Source file: `Checked/Cosmography/FREta.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 15
