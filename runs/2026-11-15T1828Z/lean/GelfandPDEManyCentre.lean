import Mathlib

/-! Gelfand problem in the three-dimensional ball as a PDE, `GelfandPDEManyCentre` (FROZEN by run
2026-11-15T1828Z before proof).

Replaces `Work/Math/GelfandPDEMany.lean` (same run), whose statement the referee of this run showed to say
nothing beyond existence (`runs/2026-11-15T1828Z/referee/REPORT.md`, Translation error): its distinctness
(`Function.Injective u`, `u ≠ v`) compares functions on all of ℝ³, while every condition of the solution
class reads only the closed ball (the Laplacian at a point of the open ball only the germ there), so one
solution altered outside the closed ball gives an "injective sequence" of solutions. Here distinct
solutions must differ at the centre of the ball, a point of the open ball.

Same PDE and solution class as `Checked/Math/GelfandPDE.lean` (headline `gelfand_pde_radial_bound`) and
`Checked/Math/GelfandPDEExists.lean` (headline `gelfand_pde_radial_exists`): u twice continuously
differentiable on the open unit ball of ℝ³ (`EuclideanSpace ℝ (Fin 3)`), continuous on the closed ball, zero
on the unit sphere, a function of ‖x‖ on the closed ball, and Δu + λ eᵘ = 0 on the open ball (Δ is Mathlib's
Laplacian).

Claim (Joseph and Lundgren 1973 for dimensions 3 to 9, stated here for dimension 3): (i) for λ = 2 there is a
sequence of radial solutions with pairwise distinct values at the centre; (ii) for every N there is ε > 0
such that every λ with |λ − 2| < ε has N radial solutions with pairwise distinct values at the centre;
(iii) every λ with 2 ≤ λ < 3.321992118 has two radial solutions with distinct values at the centre.

Route (planned, no new certificates): take the global regular solution W of w'' + (2/s) w' + e^w = 0,
w(0) = 0 (`Checked.Math.BEGlobalExists.exists_global`); for every s > 0 with s² e^{W(s)} = λ the function
u(x) = W(s‖x‖) + log(s²/λ) is a radial solution for λ (`radial_global` in
`Work/Math/GelfandPDEManyMain.lean`), and its value at the centre is log(s²/λ), strictly increasing in s.
The radii come from `Checked.Math.GelfandExtrema.gelfand_extrema` by the intermediate value theorem on the
segments between consecutive turning points, as in `Work/Math/GelfandPDEManyMain.lean`. -/

namespace Work.Math.GelfandPDEManyCentre
open Set Filter Topology InnerProductSpace Laplacian Metric

/-- Gelfand problem in the unit ball of three-dimensional space, multiplicity of radial solutions told
apart by their values at the centre: infinitely many for λ = 2, at least N for λ close enough to 2, at
least two for 2 ≤ λ < 3.321992118. -/
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
  sorry

end Work.Math.GelfandPDEManyCentre
