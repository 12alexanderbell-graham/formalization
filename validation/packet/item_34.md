# Item 34

**Area:** F3

**Source:** Capozziello, Cardone, Salzano, PRD 78, 063504 (2008), arXiv:0802.1583v2, App. A, Eq. (A2): lookback-distance z⁵ coefficient, 7/2 q₀⁴ should be 7/8 q₀⁴

## Claim in plain words (the system's own text)

The past-only reading of the printed claim is false (de Sitter).

## Formal statement (Lean 4)

```lean
theorem ccsD4ClaimPast_false : ¬ CCSD4ClaimPast := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.redshift`, `Cosmography.CCS.CCSD4ClaimPast`, `Cosmography.CCS.D1`, `Cosmography.CCS.D2`, `Cosmography.CCS.D3`, `Cosmography.CCS.printedD4`, `Cosmography.CCS.remainder`, `Cosmography.CCS.series`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, decel, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): CCSD4ClaimPast, D1², D2², D3², printedD4².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Source file: `Checked/Cosmography/CCSLookback.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 34
