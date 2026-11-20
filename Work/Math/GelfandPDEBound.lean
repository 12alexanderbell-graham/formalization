import Mathlib
import Checked.Math.GSymFree

/-! Gelfand problem in the three-dimensional ball as a PDE, `GelfandPDEBound`: the bound on the parameter of
`Checked.Math.GelfandPDE.gelfand_pde_radial_bound` for every classical solution u, with no symmetry hypothesis on u
(FROZEN by run 2026-11-20T2228Z before its proof). The route is
`Checked.Math.GSymFree.bound_no_radial`: the minimal solution below u is radial, and the radial bound applies to
it. -/

namespace Work.Math.GelfandPDEBound
open Set Filter Topology InnerProductSpace Laplacian Metric

/-- Gelfand problem in the unit ball of three-dimensional space, classical solutions with no symmetry
hypothesis: if u is twice continuously differentiable on the open unit ball, continuous on the closed unit ball
and zero on the unit sphere, and Δu + λ eᵘ = 0 on the open ball (Δ is Mathlib's Laplacian), then
λ ≤ 3.321992119. -/
theorem gelfand_pde_bound (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hu : ContDiffOn ℝ 2 u (ball 0 1))
    (hc : ContinuousOn u (closedBall 0 1))
    (hb : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (hpde : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0) :
    lam ≤ 3.321992119 := by
  exact Checked.Math.GSymFree.bound_no_radial lam u hu hc hb hpde

end Work.Math.GelfandPDEBound
