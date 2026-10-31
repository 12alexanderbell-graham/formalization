# Item 13

**Area:** F11

**Source:** Demianski, Piedipalumbo, Sawant, Amati, A&A 598, A113 (2017), arXiv:1609.09631 (v1, v2), p. 3: flat z-series D⁴_L has −105q₀⁴ (should be +105q₀⁴) and D⁴_A (Eq. (23)) has +137j₀ (should be −137j₀); the D⁴_L error is reprinted in Lusso et al., A&A 628, L4 (2019), arXiv:1907.07692 (v1–v4), the quasar+SN+GRB paper claiming > 4σ tension with flat ΛCDM

## Claim in plain words (the system's own text)

The flat `d_L(z)` series printed by Demianski et al. 2017 (and Lusso et al. 2019), with its printed
`D⁴_L`, is not `d_L + o(z⁵)` for every analytic, everywhere positive flat scale factor with `H₀ > 0`:
the claim is false.

## Formal statement (Lean 4)

```lean
theorem demDLzClaim_false : ¬ DemDLzClaim := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.BambaK.lumDist`, `Cosmography.BambaZ.curvK`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.redshift`, `Cosmography.BambaZ.DL1z`, `Cosmography.BambaZ.DL2z`, `Cosmography.BambaZ.DL3z`, `Cosmography.DemianskiZ.DemDLzClaim`, `Cosmography.DemianskiZ.demDL4`, `Cosmography.BambaY.comoving`, `Cosmography.BambaZ.remLz`, `Cosmography.BambaZ.seriesZ`, `Cosmography.Transverse.transverse`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, lumDist, curvK, decel, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): DL1z², DL2z², DL3z², DemDLzClaim, demDL4².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Source file: `Checked/Cosmography/DemianskiZ.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 13
