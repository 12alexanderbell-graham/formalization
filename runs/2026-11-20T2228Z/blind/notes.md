# Interpretive choices

- Domain: `E3 := EuclideanSpace ℝ (Fin 3)`; u : E3 → ℝ (total function, only its values on the closed ball matter for the hypotheses, except through the Laplacian, see below).
- Solution class: `ContDiffOn ℝ 2 u (ball 0 1)` (C^2 on the open ball) and `ContinuousOn u (closedBall 0 1)`. No symmetry (radial) assumed; u is a general function on E3.
- Equation: for every x in `ball 0 1`, `InnerProductSpace.laplacian u x + lam * Real.exp (u x) = 0` (this is the `Δ` of Mathlib; I wrote the name rather than the notation). Since the ball is open and u is C^2 there, the global Mathlib Laplacian agrees at interior points with the classical one.
- Boundary condition: `u x = 0` for all x in `sphere 0 1`.
- Sign convention: Δu + λ e^u = 0 with the standard (positive-semidefinite-negative) Laplacian, i.e. sum of second partials; solutions exist for 0 < λ ≤ λ*.
- λ ranges over all reals (no positivity hypothesis); for λ ≤ 0 the conclusion is trivially true since 3.32 > 0.
- Constant 3.321992119 written as a real literal (elaborated in ℝ).
- Statement: existence of a classical solution implies `lam ≤ 3.321992119`. Proof is `sorry`; nothing compiled.
