import Mathlib

open Metric InnerProductSpace

namespace GelfandBlind

/-- Radial classical solution of `Δu + λ e^u = 0` in the unit ball of ℝ³, `u = 0` on the sphere. -/
def IsRadialClassicalSolution (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ) : Prop :=
  ContDiffOn ℝ 2 u (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
  ContinuousOn u (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
  (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
  (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1,
    ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, ‖x‖ = ‖y‖ → u x = u y) ∧
  (∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1,
    InnerProductSpace.laplacian u x + lam * Real.exp (u x) = 0)

/-- Solutions up to agreement on the closed ball: the set of restrictions to the closed ball. -/
def solutionClasses (lam : ℝ) : Set (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ) :=
  {f | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ, IsRadialClassicalSolution lam u ∧
    f = fun x => u x}

theorem blind_gelfand_pde_count_values :
    ∃ lamStar lam1 lam2 : ℝ,
      (3.321992118 : ℝ) ≤ lamStar ∧ lamStar ≤ 3.321992119 ∧
      (1.664155 : ℝ) ≤ lam1 ∧ lam1 ≤ 1.664157 ∧
      (2.10852 : ℝ) ≤ lam2 ∧ lam2 ≤ 2.10858 ∧
      (∀ lam : ℝ, lamStar < lam → (solutionClasses lam).encard = 0) ∧
      (solutionClasses lamStar).encard = 1 ∧
      (∀ lam : ℝ, lam2 < lam → lam < lamStar → (solutionClasses lam).encard = 2) ∧
      (∀ lam : ℝ, 0 < lam → lam < lam1 → (solutionClasses lam).encard = 1) ∧
      (solutionClasses lam1).encard = 2 ∧
      (solutionClasses lam2).encard = 3 := by
  sorry

end GelfandBlind
