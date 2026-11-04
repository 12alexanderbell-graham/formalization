# Item 42

**Area:** F8

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Eqs. (10.38)–(10.51), verbatim from Capozziello & Salzano 2009 (arXiv:0902.0088) Eqs. (31)–(52): z-redshift d_L and d_A fourth-order coefficients D⁴_L, D⁴_A miss the curvature-squared term

## Claim in plain words (the system's own text)

The review's claim (10.45)–(10.51) is false even for past emission only (`t → t₀⁻`): see
`bambaDAzClaim_false`.

## Formal statement (Lean 4)

```lean
theorem bambaDAzClaimPast_false : ¬ BambaDAzClaimPast := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.BambaA.angDist`, `Cosmography.BambaZ.curvK`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.redshift`, `Cosmography.BambaZ.BambaDAzClaimPast`, `Cosmography.BambaZ.DA1z`, `Cosmography.BambaZ.DA2z`, `Cosmography.BambaZ.DA3z`, `Cosmography.BambaZ.printedDA4z`, `Cosmography.BambaK.lumDist`, `Cosmography.BambaY.comoving`, `Cosmography.BambaZ.remAz`, `Cosmography.BambaZ.seriesZ`, `Cosmography.Transverse.transverse`, `changed;.Checked.Chemistry.CoexistenceReduced.q`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, angDist, curvK, decel, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): BambaDAzClaimPast, DA1z², DA2z², DA3z², printedDA4z².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Source file: `Checked/Cosmography/BambaZ.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 42
