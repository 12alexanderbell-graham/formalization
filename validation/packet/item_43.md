# Item 43

**Area:** Mathematics

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `lam : ℝ`, `u : EuclideanSpace ℝ (Fin 3) → ℝ`:

**assuming**

1. `ContDiffOn ℝ 2 u (Metric.ball 0 1)`
2. `ContinuousOn u (Metric.closedBall 0 1)`
3. for every `x : EuclideanSpace ℝ (Fin 3)`, if `‖x‖ = 1`, then `u x = 0`
4. there is `g : ℝ → ℝ` such that for every `x : EuclideanSpace ℝ (Fin 3)`, if `x ∈ Metric.closedBall 0 1`, then `u x = g ‖x‖`
5. for every `x : EuclideanSpace ℝ (Fin 3)`, if `x ∈ Metric.ball 0 1`, then `Laplacian.laplacian u x + lam * Real.exp (u x) = 0`

**then**

- `lam ≤ 3.321992119`

## Author's paraphrase (hand-written; checked only by prose rules)

Gelfand problem in the unit ball of three-dimensional space, radial solutions: if u is twice
continuously differentiable on the open unit ball, continuous on the closed unit ball, zero on the unit sphere
and a function of ‖x‖ on the closed ball, and Δu + λ eᵘ = 0 on the open ball (Δ is Mathlib's Laplacian),
then λ ≤ 3.321992119.

## Formal statement (Lean 4)

```lean
theorem gelfand_pde_radial_bound (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hu : ContDiffOn ℝ 2 u (ball 0 1))
    (hc : ContinuousOn u (closedBall 0 1))
    (hb : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (hrad : ∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖)
    (hpde : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0) :
    lam ≤ 3.321992119 := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `gelfand_pde_radial_bound`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Math/GelfandPDE.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 43
