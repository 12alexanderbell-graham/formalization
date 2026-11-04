# Item 47

**Area:** Data claim

**Source:** see the claim

## Claim in plain words (the system's own text)

With the prior 73.8 ± 2.4, the marginalised chi-square of the Farooq–Ratra 2013 table
attains its smallest value over Ω in [0, 1]: there is a minimiser.

## Formal statement (Lean 4)

```lean
theorem fr13_exists738 : ∃ Ω ∈ Set.Icc (0 : ℝ) 1,
    ∀ Ω' ∈ Set.Icc (0 : ℝ) 1,
      margChiSq fr13Table 73.8 2.4 Ω ≤ margChiSq fr13Table 73.8 2.4 Ω' := …
```

## Definitions it uses

See GLOSSARY.md: `Data.FR13.fr13Table`, `Data.FR13.chiSqHz`, `Data.FR13.margChiSq`, `Data.FR13Certs.tbl`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): fr13Table.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): margChiSq: Hbar = 73.8, σ = 2.4.
- Source file: `Checked/Data/FR13.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 47
