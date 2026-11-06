# Item 04

**Area:** Mathematics

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**It holds that**

- there is `θ : ℝ → ℝ` such that there is `φ : ℝ → ℝ` such that (for every `ξ : ℝ`, if `ξ ∈ Set.Icc 0 7`, then `HasDerivWithinAt θ (φ ξ) (Set.Icc 0 7) ξ`) and (`ContinuousWithinAt φ (Set.Icc 0 7) 0`) and (for every `ξ : ℝ`, if `ξ ∈ Set.Ioc 0 7`, then `HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ 3) (Set.Icc 0 7) ξ`) and (`θ 0 = 1`)

## Author's paraphrase (hand-written; checked only by prose rules)

There exist θ, φ with θ differentiable within [0, 7] with derivative φ, φ continuous at 0,
φ' = −(2/ξ)φ − θ³ on (0, 7] and θ(0) = 1: the hypotheses of the Lane–Emden headline
`Checked.Math.LaneEmden.laneEmden3_constants` are satisfied together (a solution regular at the centre
exists).

## Formal statement (Lean 4)

```lean
theorem exists_solution : ∃ θ φ : ℝ → ℝ,
    (∀ ξ ∈ Icc (0 : ℝ) 7, HasDerivWithinAt θ (φ ξ) (Icc 0 7) ξ) ∧
    ContinuousWithinAt φ (Icc 0 7) 0 ∧
    (∀ ξ ∈ Ioc (0 : ℝ) 7, HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ 3) (Icc 0 7) ξ) ∧
    θ 0 = 1 := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Math/LEExists.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 04
