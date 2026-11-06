import Mathlib

open Laplacian Metric

namespace Blind.GelfandPDE

/-- Gelfand problem `Δu + λ e^u = 0` in the unit ball of ℝ³, `u = 0` on the sphere:
no radially symmetric classical solution when `λ > 3.321992119`. -/
theorem no_radial_solution (lam : ℝ) (hlam : 3.321992119 < lam)
    (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hC2 : ContDiffOn ℝ 2 u (ball (0 : EuclideanSpace ℝ (Fin 3)) 1))
    (hcont : ContinuousOn u (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1))
    (hpde : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)
    (hbdry : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (hrad : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1,
            ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, ‖x‖ = ‖y‖ → u x = u y) :
    False := by sorry

end Blind.GelfandPDE
