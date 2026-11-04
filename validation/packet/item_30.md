# Item 30

**Area:** Data claim

**Source:** see the claim

## Claim in plain words (the system's own text)

With the prior 68 ± 2.8, at every minimiser Ω over [0, 1] of the marginalised chi-square
of the Farooq–Ratra 2013 table, the z > −1 solving Ω(1+z)³ = 2(1 − Ω) lies strictly between
0.703 and 0.706.

## Formal statement (Lean 4)

```lean
theorem fr13_zda68 (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (hmin : ∀ Ω' ∈ Set.Icc (0 : ℝ) 1, margChiSq fr13Table 68 2.8 Ω ≤ margChiSq fr13Table 68 2.8 Ω')
    (z : ℝ) (hz : -1 < z) (hda : Ω * (1 + z) ^ 3 = 2 * (1 - Ω)) :
    0.703 < z ∧ z < 0.706 := …
```

## Definitions it uses

See GLOSSARY.md: `Data.FR13.fr13Table`, `Data.FR13.chiSqHz`, `Data.FR13.margChiSq`, `Data.FR13Certs.tbl`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): fr13Table.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `fr13_zda68`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): margChiSq: Hbar = 68, σ = 2.8.
- Source file: `Checked/Data/FR13.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 30
