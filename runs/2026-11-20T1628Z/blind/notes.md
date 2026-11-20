# Interpretive choices (blind)

- Domain: `EuclideanSpace ℝ (Fin 3)`; unit ball `Metric.ball 0 1`, closed ball `Metric.closedBall 0 1`, sphere `‖x‖ = 1`.
- Solution class `IsRadialSol l u`: `ContDiffOn ℝ 2 u (ball 0 1)`; `ContinuousOn u (closedBall 0 1)`; `u x = 0` when `‖x‖ = 1`;
  radial on the closed ball: for x, y in closedBall with `‖x‖ = ‖y‖`, `u x = u y`; PDE `Δ u x + l * Real.exp (u x) = 0` for x in the open ball
  (`Δ` is `InnerProductSpace.laplacian`, scoped notation; global Laplacian of u, but only evaluated at interior points, which is a local quantity).
- `N l`: `Set.encard` (in `ℕ∞`) of the image of the solution set under `Set.restrict (closedBall 0 1)`, so solutions agreeing on the closed ball are identified.
- "Infinite": `N 2 = ⊤`.
- Sequence: `lam : ℕ → ℝ` (named `lam` and `l` since `λ` is reserved). Bounds as closed inequalities with decimal literals.
  Even subsequence `StrictAnti (fun k => lam (2*k))`, odd `StrictMono (fun k => lam (2*k+1))`; `lam (2k+1) < 2 < lam (2k)`; `Tendsto lam atTop (𝓝 2)`.
- Counts are stated with ℕ-casts to ℕ∞, e.g. `((2*k+2 : ℕ) : ℕ∞)`.
- (a) `∀ l, lam 0 < l → N l = 0`; (e) requires `0 < l`; (c) uses k ≥ 0 ranges over all ℕ; (g) interval `lam (2k+1) < l < lam (2k+3)`.
- Existential over the whole sequence; a single theorem with a big conjunction. Not compiled.
