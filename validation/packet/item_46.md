# Item 46

**Area:** F1

**Source:** arXiv:1903.11433, Eq. (21): misprinted flat ΛCDM l₀ (printed as 1 + 3Ω_m − (27/2)Ω_m²)

## Claim in plain words (the system's own text)

**Refutation of the printed l₀ in Eq. (21).** On Einstein–de Sitter (Ω = 1) the printed
formula gives `−19/2`, the true value is `35/2`.

## Formal statement (Lean 4)

```lean
theorem avilesL0Claim_false : ¬ AvilesL0Claim := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.IsFlatLCDM`, `Cosmography.Aviles.cosmoCoeff`, `Cosmography.Aviles.AvilesL0Claim`, `Cosmography.hubble`, `Cosmography.redshift`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsFlatLCDM, cosmoCoeff.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): AvilesL0Claim.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Source file: `Checked/Cosmography/LCDMCoefficients.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 46
