import Mathlib
import Work.Math.RadialLaplacian
import Work.Math.GelfandODEBound

/-!
# Mathematics (THE RESULT part 5): the Gelfand problem in the unit ball of ℝ³ as a PDE —
# nonexistence of radial solutions above the certified bound

**Question.** The Gelfand (Frank-Kamenetskii) problem is Δu + λ eᵘ = 0 in the unit ball B of ℝ³,
u = 0 on the sphere ∂B. `Checked.Math.Gelfand.gelfand_ball_critical` certifies a statement about the
radial ODE w'' + (2/s) w' + eʷ = 0, w(0) = 0: the maximum of s² e^{w(s)}. What links that ODE
statement to the PDE (the radial Laplacian in ℝ³, the scaling u(r) = w(k r) − w(k), λ = k² e^{w(k)},
solutions with k < 41/10 that the ODE statement does not see) was prose until now.

**What is stated here** (frozen before the proof is committed, annex 40.1). For every real λ and
every u : ℝ³ → ℝ that is twice continuously differentiable on the open unit ball, continuous on the
closed unit ball, zero on the unit sphere, radial on the closed ball (u x = g ‖x‖ for some g), and
solves Δu x + λ e^{u x} = 0 at every x of the open ball, with Δ Mathlib's Laplacian on
`EuclideanSpace ℝ (Fin 3)`: λ ≤ 3.321992119.

**Not stated here:** existence of a radial solution for every 0 < λ ≤ 3.321992118 (the other half of
"λ* is the supremum of solvable λ"); that every classical solution is radial (Gidas–Ni–Nirenberg);
non-radial or weak solutions.

Only Mathlib definitions occur in the statement (no program definition to pin).
-/

namespace Work.Math.GelfandPDE
open Set Filter Topology InnerProductSpace Laplacian Metric

/-- Gelfand problem in the unit ball of ℝ³, radial solutions: if u is twice continuously
differentiable on the open unit ball, continuous on the closed unit ball, zero on the unit sphere,
a function of ‖x‖ alone on the closed ball, and Δu + λ eᵘ = 0 holds at every point of the open ball
(Δ is Mathlib's Laplacian), then λ ≤ 3.321992119. -/
theorem gelfand_pde_radial_bound (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hu : ContDiffOn ℝ 2 u (ball 0 1))
    (hc : ContinuousOn u (closedBall 0 1))
    (hb : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (hrad : ∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖)
    (hpde : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0) :
    lam ≤ 3.321992119 := by
  sorry

end Work.Math.GelfandPDE
