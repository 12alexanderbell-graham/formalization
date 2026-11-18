# Interpretive choices
- Domain: `EuclideanSpace ℝ (Fin 3)`; open ball `Metric.ball 0 1`, closed ball `Metric.closedBall 0 1`, sphere = `‖x‖ = 1`.
- Solution: `u : E3 → ℝ` with `ContDiffOn ℝ 2 u (ball 0 1)`, `ContinuousOn u (closedBall 0 1)`, `u = 0` where `‖x‖ = 1`, radial on the closed ball (`‖x‖ = ‖y‖ → u x = u y` for `‖x‖,‖y‖ ≤ 1`), and `Δ u x + lam * exp (u x) = 0` for every x in the open ball (`InnerProductSpace.laplacian`, notation `Δ`).
- "Same if agree on closed ball": count the set `solSet lam` of restrictions to the closed ball (functions `closedBall 0 1 → ℝ`), i.e. the image of the solutions under restriction.
- Counting: `Set.encard` equal to 0, 1, 2 (so "exactly" includes finiteness; ncard avoided since it gives 0 for infinite sets).
- Numbers: `∃ lamStar lam1 lam2` with 3.321992118 ≤ lamStar ≤ 3.321992119, 0<lam1<2<lam2<lamStar; (a) lam>lamStar: 0; (b) lamStar: 1; (c) lam2<lam<lamStar: 2; (d) 0<lam<lam1: 1.
- Not compiled; Laplacian is the global-derivative one, but only evaluated at interior points where u is C² so it is the usual one.
