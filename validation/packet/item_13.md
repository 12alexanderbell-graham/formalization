# Item 13

**Area:** F10

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Sec. XI, Eqs. (11.42)–(11.45) (p. 121), from Capozziello, Cardone, Salzano 2008 (arXiv:0802.1583) Eqs. (43)–(44) and the display after (44): the first-order deviations η₂₀ = F″(R₀)H₀⁴/F(R₀), η₃₀ = F‴(R₀)H₀⁶/F(R₀) of F(R) from GR are wrong, formulas and numbers

## Claim in plain words (the system's own text)

Printed (11.42) fails at every `Ω ∈ (0,1)` where it is defined, except the two roots of
`(54Ω² − 29Ω − 2)(27Ω² + 24Ω − 32)` (Ω ≈ 0.599, 0.731).

## Formal statement (Lean 4)

```lean
theorem printedEta20_false_at {Ω : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1) (hd : printedDen Ω ≠ 0)
    (hne : (54 * Ω ^ 2 - 29 * Ω - 2) * (27 * Ω ^ 2 + 24 * Ω - 32) ≠ 0) :
    ¬ HasDerivAt (eta20 Ω) (printed20 Ω) 0 := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.FRCosmo.P0`, `Cosmography.FRCosmo.P2`, `Cosmography.FRCosmo.Q0`, `Cosmography.FRCosmo.Q2`, `Cosmography.FREta.jL`, `Cosmography.FREta.lL`, `Cosmography.FREta.printed20`, `Cosmography.FREta.printedDen`, `Cosmography.FREta.qL`, `Cosmography.FREta.sL`, `Cosmography.FREta.eta20`, `Cosmography.FREta.eta20Of`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): P0², P2², Q0², Q2², jL, lL², printed20², printedDen², qL², sL².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `printedEta20_false_at`.
- Source file: `Checked/Cosmography/FREta.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 13
