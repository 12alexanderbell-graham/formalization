import Checked.Math.GelfandPDEManyMain

/-! Gelfand problem in the three-dimensional ball as a PDE, `GelfandPDEManyCentre`: multiplicity of radial classical solutions, told apart by their values at the centre of the ball — a sequence of them at the parameter of the singular solution, as many as wanted for every parameter close enough to it, and two from that parameter up to the lower end of the window of the critical parameter of `Checked.Math.GelfandPDE.gelfand_pde_radial_bound`. Promoted from `Work/Math/GelfandPDEManyCentre.lean` (frozen, proved and audited by run 2026-11-15T1828Z; an earlier freeze that compared the solutions outside the ball fell to the referee); the route is `GelfandPDEManyMain`. -/

namespace Checked.Math.GelfandPDEManyCentre
open Set Filter Topology InnerProductSpace Laplacian Metric

/-- Gelfand problem in the unit ball of three-dimensional space, radial solutions with distinct values at
the centre: there is a sequence of functions that are twice continuously differentiable on the open unit
ball, continuous on the closed unit ball, zero on the unit sphere and a function of ‖x‖ on the closed ball,
satisfy Δf + 2 e^f = 0 on the open ball (Δ is Mathlib's Laplacian) and have pairwise distinct values at the
centre; for every N there is ε > 0 such that for every lam with |lam − 2| < ε there are N such functions
satisfying Δf + lam e^f = 0 with pairwise distinct values at the centre; and for every lam with
2 ≤ lam < 3.321992118 there are two such functions satisfying Δf + lam e^f = 0 with distinct values at the
centre. -/
theorem gelfand_pde_radial_many_centre :
    (∃ u : ℕ → EuclideanSpace ℝ (Fin 3) → ℝ, Function.Injective (fun i => u i 0) ∧ ∀ i : ℕ,
      ContDiffOn ℝ 2 (u i) (ball 0 1) ∧
      ContinuousOn (u i) (closedBall 0 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u i x = 0) ∧
      (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u i x = g ‖x‖) ∧
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ (u i) x + 2 * Real.exp (u i x) = 0)) ∧
    (∀ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ lam : ℝ, |lam - 2| < ε →
      ∃ u : Fin N → EuclideanSpace ℝ (Fin 3) → ℝ, Function.Injective (fun i => u i 0) ∧ ∀ i : Fin N,
        ContDiffOn ℝ 2 (u i) (ball 0 1) ∧
        ContinuousOn (u i) (closedBall 0 1) ∧
        (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u i x = 0) ∧
        (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u i x = g ‖x‖) ∧
        (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ (u i) x + lam * Real.exp (u i x) = 0)) ∧
    (∀ lam : ℝ, 2 ≤ lam → lam < 3.321992118 →
      ∃ u v : EuclideanSpace ℝ (Fin 3) → ℝ, u 0 ≠ v 0 ∧
        (ContDiffOn ℝ 2 u (ball 0 1) ∧
          ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)) ∧
        (ContDiffOn ℝ 2 v (ball 0 1) ∧
          ContinuousOn v (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → v x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ v x + lam * Real.exp (v x) = 0))) := by
  exact Checked.Math.GelfandPDEManyMain.main_centre

end Checked.Math.GelfandPDEManyCentre
