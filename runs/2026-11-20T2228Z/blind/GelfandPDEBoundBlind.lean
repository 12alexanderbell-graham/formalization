import Mathlib

open Metric

/-- Euclidean 3-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- `u` is a classical solution of the Gelfand–Bratu problem
`Δu + λ eᵘ = 0` in the open unit ball of ℝ³, `u = 0` on the unit sphere. -/
def IsClassicalGelfandSolution (lam : ℝ) (u : E3 → ℝ) : Prop :=
  ContDiffOn ℝ 2 u (ball (0 : E3) 1) ∧
  ContinuousOn u (closedBall (0 : E3) 1) ∧
  (∀ x ∈ ball (0 : E3) 1,
    InnerProductSpace.laplacian u x + lam * Real.exp (u x) = 0) ∧
  (∀ x ∈ sphere (0 : E3) 1, u x = 0)

theorem blind_gelfand_pde_bound (lam : ℝ)
    (h : ∃ u : E3 → ℝ, IsClassicalGelfandSolution lam u) :
    lam ≤ 3.321992119 := by
  sorry
