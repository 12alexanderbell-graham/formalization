import Mathlib

/-! Gelfand problem in the three-dimensional ball as a PDE, `GelfandPDECountValues`: the exact counts of
radial classical solutions of `Checked.Math.GelfandPDECount.gelfand_pde_radial_count` with the two band ends
enclosed by numbers (FROZEN by run 2026-11-18T1028Z before its proof). The frozen statement of the parent
headline only bounds lam1 below two and lam2 above two; here lam1, the first minimum of the branch parameter
λ(s) = s² e^{W(s)} of the regular isothermal solution W, and lam2, its second maximum, are enclosed to six
and five decimals, the count clauses unchanged.

Planned route: certified cells in the homology variables u = s e^W / (−W′), v = −s W′ (the cells of
`Checked.Math.BEHCell`, with new invariants v > 2, v < 2, u < 1, u > 1) from the start enclosure of
`Checked.Math.GCerts.chain` at the first turning point to beyond the third; the turning points are the zeros of
v − 2 and λ = u v; at a zero λ = 2u, read off the cell holding it; the zeros are identified with those of
`gelfand_extrema` by comparing strict monotonicity of λ on overlapping intervals. Then the count proof of
`Checked.Math.GelfandPDECountMain` with these values. -/

namespace Work.Math.GelfandPDECountValues
open Set Filter Topology InnerProductSpace Laplacian Metric

/-- Gelfand problem in the unit ball of three-dimensional space, exact number of radial solutions. A radial
solution for the parameter lam is a function f that is twice continuously differentiable on the open unit
ball, continuous on the closed unit ball, zero on the unit sphere and a function of ‖x‖ on the closed ball,
with Δf + lam e^f = 0 on the open ball (Δ is Mathlib's Laplacian). There are numbers lamStar between
3.321992118 and 3.321992119, lam1 between 1.664155 and 1.664157 and lam2 between 2.10852 and
2.10858 such that: for
lam > lamStar there is no radial solution; for lam = lamStar there is one, and every radial solution equals it
on the closed ball; for every lam with lam2 < lam < lamStar there are two with distinct values at the centre,
and every radial solution equals one of them on the closed ball; for every lam with 0 < lam < lam1 there is
one, and every radial solution equals it on the closed ball; for lam = lam1 there are two with distinct values
at the centre and for lam = lam2 three with pairwise distinct values at the centre, and every radial solution
equals one of them on the closed ball (so lam1 and lam2 are the ends of the bands). -/
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
  sorry

end Work.Math.GelfandPDECountValues
