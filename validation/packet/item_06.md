# Item 06

**Area:** F10

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Sec. XI, Eqs. (11.42)–(11.45) (p. 121), from Capozziello, Cardone, Salzano 2008 (arXiv:0802.1583) Eqs. (43)–(44) and the display after (44): the first-order deviations η₂₀ = F″(R₀)H₀⁴/F(R₀), η₃₀ = F‴(R₀)H₀⁶/F(R₀) of F(R) from GR are wrong, formulas and numbers

## Claim in plain words (the system's own text)

The two ratios are the review's expressions in every model (no `≈`).

## Formal statement (Lean 4)

```lean
theorem eta_ratios (Ω : ℝ) (a F : ℝ → ℝ) (t₀ : ℝ) (hM : IsFRCosmo Ω a F t₀)
    (hF : F (curv a t₀) ≠ 0)
    (hR : correctR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) ≠ 0)
    (hJ : cosmoCoeff 3 a t₀ - decel a t₀ - 2 ≠ 0) :
    deriv^[2] F (curv a t₀) * hubble a t₀ ^ 4 / F (curv a t₀) =
      eta20Of Ω (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) ∧
    deriv^[3] F (curv a t₀) * hubble a t₀ ^ 6 / F (curv a t₀) =
      eta30Of Ω (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.FRCosmo.FriedmannEq`, `Cosmography.FRCosmo.MasterEq`, `Cosmography.FRCosmo.curv`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.FRCosmo.P0`, `Cosmography.FRCosmo.P2`, `Cosmography.FRCosmo.P3`, `Cosmography.FRCosmo.Q0`, `Cosmography.FRCosmo.Q2`, `Cosmography.FRCosmo.Q3`, `Cosmography.FRCosmo.IsFRCosmo`, `Cosmography.FRCosmo.correctR`, `Cosmography.FRCosmo.rhoM`, `Cosmography.FREta.eta20Of`, `Cosmography.FREta.eta30Of`, `changed;.Checked.Chemistry.CoexistenceReduced.q`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, FriedmannEq, MasterEq, curv, decel, hubble.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): P0², P2², P3², Q0², Q2², Q3².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `eta_ratios`.
- Source file: `Checked/Cosmography/FREta.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 06
