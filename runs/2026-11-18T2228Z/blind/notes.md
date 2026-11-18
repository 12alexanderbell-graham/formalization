# Interpretive choices (blind)
- Space: `EuclideanSpace ℝ (Fin 3)`; unit ball `Metric.ball 0 1`, closed ball `Metric.closedBall 0 1`; sphere is `‖x‖ = 1`.
- Solution class: `u : E3 → ℝ` with `ContDiffOn ℝ 2` on the open ball, `ContinuousOn` on the closed ball, `u x = 0` when `‖x‖ = 1`, radial on the closed ball (`‖x‖ = ‖y‖ → u x = u y` for x, y in the closed ball), and `laplacian u x + lam * exp (u x) = 0` for x in the open ball.
- Laplacian: written `InnerProductSpace.laplacian u x` (full name, no `Δ` notation, to avoid scoping issues). Name or signature may need adjusting.
- "Counted as the same": N lam is the `Set.encard` of the image of the solution set under restriction to the closed ball (`Set.restrict`), so solutions agreeing there are identified.
- N has type `ℕ∞`; "infinite" is stated as `N 2 = ⊤`. Finite counts are casts of naturals.
- The sequence is `l : ℕ → ℝ`. Numeric bounds on l 0, l 1, l 2 are stated with decimal literals. Even terms: `StrictAnti (fun k => l (2*k))`; odd terms: `StrictMono (fun k => l (2*k+1))`. `l (2k+1) < 2 < l (2k)` for all k. Convergence: `Tendsto l atTop (𝓝 2)`.
- (e) uses 0 < lam < l 1. (c) uses l(2k+2) < lam < l(2k); (g) uses l(2k+1) < lam < l(2k+3).
- (a) `N lam = 0` for lam > l 0 (no extra hypotheses).
- The claim is existential over the sequence l; the theorem is `sorry` (not compiled).
