import Mathlib

/-! Blind restatement of the exact-count claim with numerical band ends for the Gelfand problem (run 2026-11-18T1028Z, Sonnet, brief `runs/2026-11-18T1028Z/blind/BRIEF.md`), copied verbatim from `runs/2026-11-18T1028Z/blind/GelfandPDECountValuesBlind.lean` with the namespace renamed and two compile repairs that keep its meaning: `InnerProductSpace.laplacian u x` (not a Mathlib name) written `Δ u x` under `open Laplacian` (the brief's notation for Mathlib's Laplacian), and the binder of `fun x => u x` given the subtype of the closed ball that its left-hand side already has. -/

open Metric InnerProductSpace Laplacian

namespace Work.Math.GelfandPDECountValuesBlind

/-- Radial classical solution of `Δu + λ e^u = 0` in the unit ball of ℝ³, `u = 0` on the sphere. -/
def IsRadialClassicalSolution (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ) : Prop :=
  ContDiffOn ℝ 2 u (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
  ContinuousOn u (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
  (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
  (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1,
    ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, ‖x‖ = ‖y‖ → u x = u y) ∧
  (∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1,
    Δ u x + lam * Real.exp (u x) = 0)

/-- Solutions up to agreement on the closed ball: the set of restrictions to the closed ball. -/
def solutionClasses (lam : ℝ) : Set (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ) :=
  {f | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ, IsRadialClassicalSolution lam u ∧
    f = fun x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 => u x}

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

end Work.Math.GelfandPDECountValuesBlind
