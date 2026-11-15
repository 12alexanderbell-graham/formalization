# Interpretive choices
- Domain: `EuclideanSpace ℝ (Fin 3)`, open ball `Metric.ball 0 1`, closed ball `Metric.closedBall 0 1`.
- Solution class: `u : E → ℝ` with `ContDiffOn ℝ 2 u (ball 0 1)` (C^2 inside), `ContinuousOn u (closedBall 0 1)`,
  `u x = 0` for `‖x‖ = 1`, radial on the closed ball (`‖x‖ = ‖y‖ → u x = u y` for x,y in closed ball),
  and `Δ u x + lam * Real.exp (u x) = 0` for every x in the open ball (`Δ` = `InnerProductSpace.laplacian`).
- Values of u outside the closed ball are unconstrained, so distinctness is only counted on the closed ball:
  - (i) "infinitely many": `(SolRestr 2).Infinite`, where `SolRestr` is the set of restrictions of solutions to the closed ball (a set of functions on the subtype).
  - (ii) "at least N distinct": `∃ F : Fin N → (E → ℝ)` of solutions, pairwise `DistinctOnBall` (differ at some point of the closed ball); ε is chosen first, then holds for all lam with |lam - 2| < ε (lam real, ε > 0).
  - (iii) two solutions that are `DistinctOnBall`, for 2 ≤ lam < 3.321992118 (decimal literal read as a real).
- N = 0, 1 are trivially fine in (ii).
- Not compiled.
