# Item 20

**Area:** Certified numbers of the findings

**Source:** Aviles, Gruber, Luongo, Quevedo, PRD 86, 123516 (2012), arXiv:1204.2007 (v1 and v2), Eq. (15): misprinted ΛCDM l₀ and m₀

## Claim in plain words (the system's own text)

In every flat ΛCDM model with `Ω_m = 0.3`, `l₀ = 3.115` (to 3 decimals).

## Formal statement (Lean 4)

```lean
theorem F1_l0 (a : ℝ → ℝ) (t₀ : ℝ) (hL : IsFlatLCDM (3 / 10) a t₀)
    (hs : ContDiffAt ℝ 6 a t₀) : RoundsTo (cosmoCoeff 5 a t₀) 3.115 3 := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.IsFlatLCDM`, `Cosmography.Aviles.cosmoCoeff`, `Cosmography.hubble`, `Cosmography.redshift`, `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsFlatLCDM, cosmoCoeff.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `F1_l0`.
- Source file: `Checked/Records/Findings.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 20
