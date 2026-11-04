# Item 13

**Area:** F11

**Source:** Demianski, Piedipalumbo, Sawant, Amati, A&A 598, A113 (2017), arXiv:1609.09631 (v1, v2), p. 3: flat z-series D⁴_L has −105q₀⁴ (should be +105q₀⁴) and D⁴_A (Eq. (23)) has +137j₀ (should be −137j₀); the D⁴_L error is reprinted in Lusso et al., A&A 628, L4 (2019), arXiv:1907.07692 (v1–v4), the quasar+SN+GRB paper claiming > 4σ tension with flat ΛCDM

## Claim in plain words (the system's own text)

The Demianski et al. `d_A(z)` claim is false even for past emission only (`t → t₀⁻`): see
`demDAzClaim_false`.

## Formal statement (Lean 4)

```lean
theorem demDAzClaimPast_false : ¬ DemDAzClaimPast := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.BambaA.angDist`, `Cosmography.BambaZ.curvK`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.redshift`, `Cosmography.BambaZ.DA1z`, `Cosmography.BambaZ.DA2z`, `Cosmography.BambaZ.DA3z`, `Cosmography.DemianskiZ.DemDAzClaimPast`, `Cosmography.DemianskiZ.demDA4`, `Chemistry.RKReduced.q`, `Cosmography.BambaK.lumDist`, `Cosmography.BambaY.comoving`, `Cosmography.BambaZ.remAz`, `Cosmography.BambaZ.seriesZ`, `Cosmography.Transverse.transverse`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, angDist, curvK, decel, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): DA1z², DA2z², DA3z², DemDAzClaimPast, demDA4².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): angDist: K = 0; cosmoCoeff: n = 3, n = 4, n = 5; curvK: K = 0.
- Source file: `Checked/Cosmography/DemianskiZ.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 13
