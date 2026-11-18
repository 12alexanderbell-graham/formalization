import Mathlib

open Metric InnerProductSpace Laplacian

namespace GelfandBlind

/-- Euclidean 3-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- `u` is a radial classical solution of `Δu + λ e^u = 0` in the open unit ball,
`u = 0` on the unit sphere. -/
structure IsRadialSol (lam : ℝ) (u : E3 → ℝ) : Prop where
  contDiff : ContDiffOn ℝ 2 u (ball (0 : E3) 1)
  cont : ContinuousOn u (closedBall (0 : E3) 1)
  bdry : ∀ x : E3, ‖x‖ = 1 → u x = 0
  radial : ∀ x y : E3, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖x‖ = ‖y‖ → u x = u y
  pde : ∀ x ∈ ball (0 : E3) 1, Δ u x + lam * Real.exp (u x) = 0

/-- Solutions identified when they agree on the closed ball: the set of restrictions
to the closed unit ball of radial classical solutions. -/
def solSet (lam : ℝ) : Set (closedBall (0 : E3) 1 → ℝ) :=
  {f | ∃ u : E3 → ℝ, IsRadialSol lam u ∧ ∀ x : closedBall (0 : E3) 1, u x = f x}

theorem blind_gelfand_pde_count :
    ∃ lamStar lam1 lam2 : ℝ,
      3.321992118 ≤ lamStar ∧ lamStar ≤ 3.321992119 ∧
      0 < lam1 ∧ lam1 < 2 ∧ 2 < lam2 ∧ lam2 < lamStar ∧
      (∀ lam : ℝ, lamStar < lam → (solSet lam).encard = 0) ∧
      (solSet lamStar).encard = 1 ∧
      (∀ lam : ℝ, lam2 < lam → lam < lamStar → (solSet lam).encard = 2) ∧
      (∀ lam : ℝ, 0 < lam → lam < lam1 → (solSet lam).encard = 1) := by
  sorry

end GelfandBlind
