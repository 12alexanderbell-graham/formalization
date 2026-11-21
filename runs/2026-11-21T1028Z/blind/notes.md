# Interpretive choices
- Domain: EuclideanSpace ℝ (Fin 3); u : E → ℝ. C^2 = ContDiffOn ℝ 2 on Metric.ball 0 1; ContinuousOn on closedBall 0 1.
- Zero on sphere: ∀ x, ‖x‖ = 1 → u x = 0.
- Radial on closed ball: ∀ x y with ‖x‖,‖y‖ ≤ 1, ‖x‖=‖y‖ → u x = u y.
- PDE: InnerProductSpace.laplacian u x + λ * exp (u x) = 0 for x in open ball (written by full name; `Δ` notation not used).
- "Same when agree on closed ball": solSet λ is the image of the solution set under restriction to the subtype closedBall; N λ = encard of it (ℕ∞).
- "Infinite": N 2 = ⊤ (equivalent to the set being infinite).
- Sequence l : ℕ → ℝ; bounds, StrictAnti on evens, StrictMono on odds, l(2k+1) < 2 < l(2k), Tendsto l atTop (nhds 2).
- Counts stated with ℕ casts into ℕ∞; (a) is for all λ > l 0 (including negatives is not an issue, none needed beyond λ>λ₀).
- (e) restricted to 0 < λ < l 1 as in claim.
