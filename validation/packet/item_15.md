# Item 15

**Area:** Mathematics/physics

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**It holds that**

- there is `y : ℝ → ℝ` such that there is `φ : ℝ → ℝ` such that (for every `x : ℝ`, if `0 ≤ x`, then `HasDerivWithinAt y (φ x) (Set.Ici 0) x`) and (for every `x : ℝ`, if `0 < x`, then `HasDerivAt φ (y x ^ (3 / 2) / √x) x`) and (`ContinuousWithinAt φ (Set.Ici 0) 0`) and (`y 0 = 1`) and (for every `x : ℝ`, if `0 ≤ x`, then `0 < y x`) and (`Filter.Tendsto y Filter.atTop (nhds 0)`)

## Author's paraphrase (hand-written; checked only by prose rules)

There is a solution y of the Thomas–Fermi equation y'' = y^{3/2}/√x on (0, ∞) with y' = φ on
[0, ∞), φ continuous at 0 from the right, y(0) = 1, y > 0 on [0, ∞) and y(x) → 0 as x → ∞.

## Formal statement (Lean 4)

```lean
theorem tf_exists : ∃ y φ : ℝ → ℝ,
    (∀ x, 0 ≤ x → HasDerivWithinAt y (φ x) (Ici 0) x) ∧
    (∀ x, 0 < x → HasDerivAt φ (y x ^ ((3 : ℝ) / 2) / Real.sqrt x) x) ∧
    ContinuousWithinAt φ (Ici 0) 0 ∧ y 0 = 1 ∧ (∀ x, 0 ≤ x → 0 < y x) ∧
    Tendsto y atTop (𝓝 0) := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Math/ThomasFermiExists.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 15
