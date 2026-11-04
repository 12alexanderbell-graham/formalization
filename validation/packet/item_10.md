# Item 10

**Area:** F10

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Sec. XI, Eqs. (11.42)–(11.45) (p. 121), from Capozziello, Cardone, Salzano 2008 (arXiv:0802.1583) Eqs. (43)–(44) and the display after (44): the first-order deviations η₂₀ = F″(R₀)H₀⁴/F(R₀), η₃₀ = F‴(R₀)H₀⁶/F(R₀) of F(R) from GR are wrong, formulas and numbers

## Claim in plain words (the system's own text)

**Correct (11.42)**: `η₂₀ = correct20(Ω)·ε` to first order.

## Formal statement (Lean 4)

```lean
theorem eta20_hasDerivAt {Ω : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1) :
    eta20 Ω 0 = 0 ∧ HasDerivAt (eta20 Ω) (correct20 Ω) 0 := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.FRCosmo.P0`, `Cosmography.FRCosmo.P2`, `Cosmography.FRCosmo.Q0`, `Cosmography.FRCosmo.Q2`, `Cosmography.FREta.jL`, `Cosmography.FREta.lL`, `Cosmography.FREta.qL`, `Cosmography.FREta.sL`, `Cosmography.FREta.correct20`, `Cosmography.FREta.eta20`, `Cosmography.FREta.eta20Of`, `changed;.Checked.Chemistry.CoexistenceReduced.q`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): P0², P2², Q0², Q2², jL, lL², qL², sL².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `eta20_hasDerivAt`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): eta20: ε = 0.
- Source file: `Checked/Cosmography/FREta.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 10
