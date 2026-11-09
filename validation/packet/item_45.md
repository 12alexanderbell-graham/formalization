# Item 45

**Area:** Mathematics/physics

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `y : ℝ → ℝ`, `φ : ℝ → ℝ`:

**assuming**

1. for every `x : ℝ`, if `0 ≤ x`, then `HasDerivWithinAt y (φ x) (Set.Ici 0) x`
2. for every `x : ℝ`, if `0 < x`, then `HasDerivAt φ (y x ^ (3 / 2) / √x) x`
3. `ContinuousWithinAt φ (Set.Ici 0) 0`
4. `y 0 = 1`
5. for every `x : ℝ`, if `0 ≤ x`, then `0 < y x`
6. `Filter.Tendsto y Filter.atTop (nhds 0)`

**then**

1. `-1.58807103 ≤ φ 0`
2. `φ 0 ≤ -1.58807102`

## Author's paraphrase (hand-written; checked only by prose rules)

Every solution y of the Thomas–Fermi equation y'' = y^{3/2}/√x on (0, ∞) with y' = φ on
[0, ∞), φ continuous at 0 from the right, y(0) = 1, y > 0 on [0, ∞) and y(x) → 0 as x → ∞ has
initial slope −1.58807103 ≤ φ(0) ≤ −1.58807102.

## Formal statement (Lean 4)

```lean
theorem tf_initial_slope (y φ : ℝ → ℝ)
    (hy : ∀ x, 0 ≤ x → HasDerivWithinAt y (φ x) (Ici 0) x)
    (hφ : ∀ x, 0 < x → HasDerivAt φ (y x ^ ((3 : ℝ) / 2) / Real.sqrt x) x)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (h0 : y 0 = 1) (hpos : ∀ x, 0 ≤ x → 0 < y x)
    (hlim : Tendsto y atTop (𝓝 0)) :
    -1.58807103 ≤ φ 0 ∧ φ 0 ≤ -1.58807102 := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `tf_initial_slope`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Math/ThomasFermi.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 45
