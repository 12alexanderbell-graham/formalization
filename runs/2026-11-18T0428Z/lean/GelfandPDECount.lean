import Mathlib

/-! Gelfand problem in the three-dimensional ball as a PDE, `GelfandPDECount`: exact counts of radial
classical solutions (FROZEN by run 2026-11-18T0428Z before its proof). lamStar is the maximum of the branch
parameter λ(s) = s² e^{W(s)} of the regular isothermal solution W, lam1 its first minimum, lam2 its second
maximum (the turning points of `Checked.Math.GelfandExtrema.gelfand_extrema`).

Planned route: (1) uniqueness of the regular singular initial-value problem w'' + (2/s)w' + e^w = 0, w(0)
given, in the class of `Checked.Math.BEGlobalExists.exists_global` (`Work.Math.IsoUniq.uniq_Icc`, proved:
a contraction near the centre through u = s²(φ₁ − φ₂), Mathlib's Lipschitz uniqueness after); (2) every radial
solution u with lam > 0 is W(s‖x‖) + log(s²/lam) on the closed ball for a radius s > 0 with
s² e^{W(s)} = lam (the reduction of `Checked.Math.GelfandPDE.gelfand_pde_radial_bound` and the scaling of
`Checked.Math.GelfandODEBound.ode_bound`, then (1) on [0, s) and continuity at s); (3) conversely every such
radius gives a radial solution (`Checked.Math.GelfandPDEManyMain.radial_global`), distinct radii give distinct
centre values; (4) count the radii with `gelfand_extrema`: strictly increasing on [0, ζ₀], strictly decreasing
on [ζ₀, ζ₁], λ(ζ₁) the smallest value from ζ₀ on, λ(ζ₂) the largest from ζ₁ on, λ(ζ₀) the strict global
maximum. For lam ≤ 0 nothing is claimed. -/

namespace Work.Math.GelfandPDECount
open Set Filter Topology InnerProductSpace Laplacian Metric

/-- Gelfand problem in the unit ball of three-dimensional space, exact number of radial solutions. A radial
solution for the parameter lam is a function f that is twice continuously differentiable on the open unit
ball, continuous on the closed unit ball, zero on the unit sphere and a function of ‖x‖ on the closed ball,
with Δf + lam e^f = 0 on the open ball (Δ is Mathlib's Laplacian). There are numbers lamStar between
3.321992118 and 3.321992119, lam1 with 0 < lam1 < 2 and lam2 with 2 < lam2 < lamStar such that: for
lam > lamStar there is no radial solution; for lam = lamStar there is one, and every radial solution equals it
on the closed ball; for every lam with lam2 < lam < lamStar there are two with distinct values at the centre,
and every radial solution equals one of them on the closed ball; for every lam with 0 < lam < lam1 there is
one, and every radial solution equals it on the closed ball. -/
theorem gelfand_pde_radial_count :
    ∃ lamStar lam1 lam2 : ℝ, 3.321992118 ≤ lamStar ∧ lamStar ≤ 3.321992119 ∧
      0 < lam1 ∧ lam1 < 2 ∧ 2 < lam2 ∧ lam2 < lamStar ∧
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
            ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = u x) := by
  sorry

end Work.Math.GelfandPDECount
