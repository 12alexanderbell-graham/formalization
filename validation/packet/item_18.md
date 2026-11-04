# Item 18

**Area:** F9

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Sec. XI ("testing F(R) gravity by cosmography"), Eq. (11.31), from Capozziello, Cardone, Salzano 2008 (arXiv:0802.1583, PRD 78, 063504) Eq. (33): the common denominator R of the F(R₀), F″(R₀), F‴(R₀) formulas is wrong, so the printed F(R₀) formula (11.21) fails the paper's own ΛCDM check (11.40); also (11.13) d³R₀/dt³ has a sign error

## Claim in plain words (the system's own text)

The review's (11.13), `d³R₀/dt³ = −6H₀⁵[l₀ − s₀ + 2(q₀ + 4)j₀ − 6(3q₀ + 8)q₀ − 24]`, does not hold for
every flat FLRW scale factor `C⁵` at `t₀` with `a(t₀) > 0`, `H₀ > 0` (the correct term is
`−2(q₀ + 4)j₀`: `curv_derivs`).

## Formal statement (Lean 4)

```lean
theorem printedR3Claim_false : ¬ PrintedR3Claim := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.FRCosmo.curv`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.FRCosmo.PrintedR3Claim`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, curv, decel, hubble.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): PrintedR3Claim.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Source file: `Checked/Cosmography/FRCosmo.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 18
