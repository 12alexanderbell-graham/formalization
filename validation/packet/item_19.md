# Item 19

**Area:** Mathematics

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `S : ℝ`:

**assuming**

1. `1 / 2 ≤ S`

**then**

- there is `w : ℝ → ℝ` such that there is `φ : ℝ → ℝ` such that (for every `s : ℝ`, if `s ∈ Set.Icc 0 S`, then `HasDerivWithinAt w (φ s) (Set.Icc 0 S) s`) and (`ContinuousWithinAt φ (Set.Icc 0 S) 0`) and (for every `s : ℝ`, if `s ∈ Set.Ioc 0 S`, then `HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Set.Icc 0 S) s`) and (`w 0 = 0`)

## Author's paraphrase (hand-written; checked only by prose rules)

For every S ≥ 1/2 there exist w, φ with w differentiable within [0, S] with derivative φ, φ
continuous at 0, φ' = −(2/s)φ − e^w on (0, S] and w(0) = 0: the hypotheses of the Gelfand
headline are satisfied together.

## Formal statement (Lean 4)

```lean
theorem exists_solution (S : ℝ) (hS : 1 / 2 ≤ S) : ∃ w φ : ℝ → ℝ,
    (∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s) ∧
    ContinuousWithinAt φ (Icc 0 S) 0 ∧
    (∀ s ∈ Ioc (0 : ℝ) S, HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s) ∧
    w 0 = 0 := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `gelfand_exists_solution`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Math/GelfandExists.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 19
