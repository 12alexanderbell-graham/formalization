# Item 08

**Area:** F6

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421 (v1–v3), Eqs. (10.55)–(10.57), copied verbatim from Capozziello & Salzano, Adv. Astron. 2009, 217420, arXiv:0902.0088, Eqs. (56)–(58): curvature terms of the y-redshift d_L coefficients D³_{L,y}, D⁴_{L,y} wrong

## Claim in plain words (the system's own text)

The review's claim (10.56)–(10.57) is false: it is not true that for every curvature `K` and every
analytic, everywhere positive scale factor with `H₀ > 0` the `d_L(y)` series with the corrected `D²`,
`D³` and the printed `D⁴_{L,y}` equals `d_L + o(y⁵)` as `t → t₀`.

## Formal statement (Lean 4)

```lean
theorem bambaD4yClaim_false : ¬ BambaD4yClaim := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.BambaK.lumDist`, `Cosmography.BambaK.omega0`, `Cosmography.BambaY.yred`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.BambaK.BambaD4yClaim`, `Cosmography.BambaK.printedD3y`, `Cosmography.BambaK.printedD4y`, `Cosmography.BambaY.D1y`, `Cosmography.BambaK.correctD3y`, `Cosmography.BambaK.remK`, `Cosmography.BambaK.seriesY4`, `Cosmography.BambaY.comoving`, `Cosmography.BambaY.correctD2y`, `Cosmography.CCS.D2`, `Cosmography.CCS.D3`, `Cosmography.Transverse.transverse`, `Cosmography.redshift`, `changed;.Checked.Chemistry.CoexistenceReduced.q`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, lumDist, omega0, yred, decel, hubble.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): BambaD4yClaim, printedD3y², printedD4y², D1y².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Source file: `Checked/Cosmography/BambaCurved.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 08
