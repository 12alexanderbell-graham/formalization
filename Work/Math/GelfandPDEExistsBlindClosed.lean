import Mathlib
import Work.Math.GelfandPDEExists
import Work.Math.GelfandPDEExistsBlind

/-! Audit of `Work.Math.GelfandPDEExists.gelfand_pde_radial_exists`: the blind restatement
(`Work.Math.GelfandPDEExistsBlind.gelfand_radial_solution_exists`) proved from the frozen
headline. -/

namespace Work.Math.GelfandPDEExistsBlindClosed
open Laplacian Metric

theorem blind_closed (lam : ℝ) (hpos : 0 < lam) (hle : lam ≤ 3.321992118) :
    ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
      ContinuousOn u (closedBall 0 1) ∧
      ContDiffOn ℝ 2 u (ball 0 1) ∧
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
      (∃ v : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = v ‖x‖) := by
  obtain ⟨u, h1, h2, h3, h4, h5⟩ :=
    Work.Math.GelfandPDEExists.gelfand_pde_radial_exists lam hpos hle
  exact ⟨u, h2, h1, h5, h3, h4⟩

/-- The hypotheses of `Work.Math.GelfandPDE.gelfand_pde_radial_bound` are met at λ = 3.321992118, so
its bound 3.321992119 cannot be lowered below 3.321992118 (non-vacuity for λ > 0). -/
theorem bound_sharp : ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
    ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
    (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
    (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
    (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1,
      Δ u x + 3.321992118 * Real.exp (u x) = 0) :=
  Work.Math.GelfandPDEExists.gelfand_pde_radial_exists 3.321992118 (by norm_num) le_rfl

end Work.Math.GelfandPDEExistsBlindClosed
