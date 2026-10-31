# Item 08

**Area:** Certified numbers of the findings

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Sec. XI, Eqs. (11.42)–(11.45) (p. 121), from Capozziello, Cardone, Salzano 2008 (arXiv:0802.1583) Eqs. (43)–(44) and the display after (44): the first-order deviations η₂₀ = F″(R₀)H₀⁴/F(R₀), η₃₀ = F‴(R₀)H₀⁶/F(R₀) of F(R) from GR are wrong, formulas and numbers

## Claim in plain words (the system's own text)

The correct first-order coefficients (`FREta.correct20`, `correct30`, the `ε`-derivatives of
η₂₀, η₃₀ by `FREta.eta20_hasDerivAt`, `eta30_hasDerivAt`) at the paper's `Ω = 0.041, 0.25`.

## Formal statement (Lean 4)

```lean
theorem F10_eta :
    RoundsTo (FREta.correct20 (41 / 1000)) (-0.249) 3 ∧
    RoundsTo (FREta.correct20 (1 / 4)) (-0.032) 3 ∧
    RoundsTo (FREta.correct30 (41 / 1000)) (-0.400) 3 ∧
    RoundsTo (FREta.correct30 (1 / 4)) (-0.0152) 4 := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.FREta.correct20`, `Cosmography.FREta.correct30`, `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Source file: `Checked/Records/Findings.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 08
