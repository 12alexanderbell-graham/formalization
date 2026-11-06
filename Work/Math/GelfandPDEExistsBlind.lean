import Mathlib


/-! Copy of the blind restatement `runs/2026-11-06T1628Z/blind/GelfandPDEExistsBlind.lean` (Sonnet,
from the words of the claim alone), namespace renamed; closed in
`Work.Math.GelfandPDEExistsBlindClosed`. -/
open Laplacian Metric

namespace Work.Math.GelfandPDEExistsBlind

theorem gelfand_radial_solution_exists (lam : ℝ) (hpos : 0 < lam)
    (hle : lam ≤ 3.321992118) :
    ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
      ContinuousOn u (closedBall 0 1) ∧
      ContDiffOn ℝ 2 u (ball 0 1) ∧
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
      (∃ v : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = v ‖x‖) := by
  sorry

end Work.Math.GelfandPDEExistsBlind
