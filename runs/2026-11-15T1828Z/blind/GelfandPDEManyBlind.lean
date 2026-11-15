import Mathlib

open InnerProductSpace Laplacian Metric

namespace GelfandBlind

/-- Radial classical solution of `Δu + λ e^u = 0` in the open unit ball of `ℝ³`,
`u = 0` on the unit sphere. -/
def IsRadialClassicalSol (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ) : Prop :=
  ContDiffOn ℝ 2 u (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
  ContinuousOn u (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
  (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
  (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1,
    ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, ‖x‖ = ‖y‖ → u x = u y) ∧
  (∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1,
    (Δ u) x + lam * Real.exp (u x) = 0)

/-- Two solutions are distinct when they differ at some point of the closed ball
(values outside the closed ball are irrelevant). -/
def DistinctOnBall (u v : EuclideanSpace ℝ (Fin 3) → ℝ) : Prop :=
  ∃ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x ≠ v x

/-- Set of solutions seen as functions on the closed ball (so that distinct elements are
genuinely distinct solutions). -/
def SolRestr (lam : ℝ) : Set (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 : ℝ) → ℝ) :=
  {v | ∃ u, IsRadialClassicalSol lam u ∧ ∀ x, v x = u x}

theorem blind_gelfand_pde_many :
    (SolRestr 2).Infinite ∧
    (∀ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ lam : ℝ, |lam - 2| < ε →
      ∃ F : Fin N → (EuclideanSpace ℝ (Fin 3) → ℝ),
        (∀ i, IsRadialClassicalSol lam (F i)) ∧
        ∀ i j, i ≠ j → DistinctOnBall (F i) (F j)) ∧
    (∀ lam : ℝ, 2 ≤ lam → lam < 3.321992118 →
      ∃ u v : EuclideanSpace ℝ (Fin 3) → ℝ,
        IsRadialClassicalSol lam u ∧ IsRadialClassicalSol lam v ∧ DistinctOnBall u v) := by
  sorry

end GelfandBlind
