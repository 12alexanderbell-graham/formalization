import Checked.Math.GelfandPDECountValuesMain

/-! Gelfand problem in the three-dimensional ball as a PDE, `GelfandPDECountValues`: the exact counts of radial classical solutions of `Checked.Math.GelfandPDECount.gelfand_pde_radial_count`, count clauses unchanged, with the two band ends (the first minimum and the second maximum of the branch parameter) enclosed by numbers. Promoted from `Work/Math/GelfandPDECountValues.lean` (frozen, proved and audited by run 2026-11-18T1028Z); the route is `GelfandPDECountValuesMain`. -/

namespace Checked.Math.GelfandPDECountValues
open Set Filter Topology InnerProductSpace Laplacian Metric

/-- Gelfand problem in the unit ball of three-dimensional space, count of radial solutions. A radial solution for the parameter lam is a function f that is twice continuously differentiable on
the open unit ball, continuous on the closed unit ball, zero on the unit sphere and a function of ‖x‖ on the
closed ball, with Δf + lam e^f = 0 on the open ball (Δ is Mathlib's Laplacian). There are numbers lamStar
between 3.321992118 and 3.321992119, lam1 between 1.664155 and 1.664157 and lam2 between 2.10852 and 2.10858
such that: for lam > lamStar there is no radial solution; for lam = lamStar there is one, u, and every radial
solution v equals u on the closed ball; for every lam with lam2 < lam < lamStar there are two with distinct
values at the centre, and every radial solution f equals one of them on the closed ball; for every lam with
0 < lam < lam1 there is one, u, and every radial solution v equals u on the closed ball; there are two with
distinct values at the centre for lam = lam1, and three with pairwise distinct values at the centre for
lam = lam2, and in both cases every radial solution f equals one of them on the closed ball. -/
theorem gelfand_pde_radial_count_values :
    ∃ lamStar lam1 lam2 : ℝ, 3.321992118 ≤ lamStar ∧ lamStar ≤ 3.321992119 ∧
      1.664155 ≤ lam1 ∧ lam1 ≤ 1.664157 ∧ 2.10852 ≤ lam2 ∧ lam2 ≤ 2.10858 ∧
      (∀ lam : ℝ, lamStar < lam → ∀ u : EuclideanSpace ℝ (Fin 3) → ℝ,
        ¬ (ContDiffOn ℝ 2 u (ball 0 1) ∧
          ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0))) ∧
      (∃ u : EuclideanSpace ℝ (Fin 3) → ℝ, (ContDiffOn ℝ 2 u (ball 0 1) ∧
          ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lamStar * Real.exp (u x) = 0)) ∧
        ∀ v : EuclideanSpace ℝ (Fin 3) → ℝ, (ContDiffOn ℝ 2 v (ball 0 1) ∧
          ContinuousOn v (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → v x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ v x + lamStar * Real.exp (v x) = 0)) →
          ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = u x) ∧
      (∀ lam : ℝ, lam2 < lam → lam < lamStar →
        ∃ u v : EuclideanSpace ℝ (Fin 3) → ℝ, u 0 ≠ v 0 ∧ (ContDiffOn ℝ 2 u (ball 0 1) ∧
          ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)) ∧ (ContDiffOn ℝ 2 v (ball 0 1) ∧
          ContinuousOn v (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → v x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ v x + lam * Real.exp (v x) = 0)) ∧
          ∀ f : EuclideanSpace ℝ (Fin 3) → ℝ, (ContDiffOn ℝ 2 f (ball 0 1) ∧
          ContinuousOn f (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → f x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ f x + lam * Real.exp (f x) = 0)) →
            (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = u x) ∨
            (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = v x)) ∧
      (∀ lam : ℝ, 0 < lam → lam < lam1 →
        ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ, (ContDiffOn ℝ 2 u (ball 0 1) ∧
          ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)) ∧
          ∀ v : EuclideanSpace ℝ (Fin 3) → ℝ, (ContDiffOn ℝ 2 v (ball 0 1) ∧
          ContinuousOn v (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → v x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ v x + lam * Real.exp (v x) = 0)) →
            ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = u x) ∧
      (∃ u v : EuclideanSpace ℝ (Fin 3) → ℝ, u 0 ≠ v 0 ∧ (ContDiffOn ℝ 2 u (ball 0 1) ∧
          ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam1 * Real.exp (u x) = 0)) ∧ (ContDiffOn ℝ 2 v (ball 0 1) ∧
          ContinuousOn v (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → v x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ v x + lam1 * Real.exp (v x) = 0)) ∧
          ∀ f : EuclideanSpace ℝ (Fin 3) → ℝ, (ContDiffOn ℝ 2 f (ball 0 1) ∧
          ContinuousOn f (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → f x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ f x + lam1 * Real.exp (f x) = 0)) →
            (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = u x) ∨ (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = v x)) ∧
      (∃ u v w : EuclideanSpace ℝ (Fin 3) → ℝ, u 0 ≠ v 0 ∧ u 0 ≠ w 0 ∧ v 0 ≠ w 0 ∧
          (ContDiffOn ℝ 2 u (ball 0 1) ∧
          ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam2 * Real.exp (u x) = 0)) ∧ (ContDiffOn ℝ 2 v (ball 0 1) ∧
          ContinuousOn v (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → v x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ v x + lam2 * Real.exp (v x) = 0)) ∧ (ContDiffOn ℝ 2 w (ball 0 1) ∧
          ContinuousOn w (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → w x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, w x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ w x + lam2 * Real.exp (w x) = 0)) ∧
          ∀ f : EuclideanSpace ℝ (Fin 3) → ℝ, (ContDiffOn ℝ 2 f (ball 0 1) ∧
          ContinuousOn f (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → f x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ f x + lam2 * Real.exp (f x) = 0)) →
            (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = u x) ∨ (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = v x) ∨ (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = w x)) :=
  Checked.Math.GelfandPDECountValuesMain.main

end Checked.Math.GelfandPDECountValues
