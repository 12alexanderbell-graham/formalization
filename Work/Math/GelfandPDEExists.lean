import Mathlib
import Checked.Math.Gelfand
import Checked.Math.GelfandExists
import Work.Math.RadialLaplacian
import Work.Math.RadialC2
import Work.Math.GProfile

/-!
# Mathematics (THE RESULT part 5): the Gelfand problem in the unit ball of ℝ³ as a PDE —
# existence of radial solutions up to the certified bound

**Question.** Companion of `Work.Math.GelfandPDE.gelfand_pde_radial_bound` (no radial classical
solution of Δu + λ eᵘ = 0 in the unit ball of ℝ³, u = 0 on the sphere, for λ > 3.321992119): for
which λ does a radial classical solution exist? Together the two statements locate the supremum λ*
of the λ with a radial solution in [3.321992118, 3.321992119].

**What is stated here** (frozen before the proof, annex 40.1). For every λ with
0 < λ ≤ 3.321992118 there is u : ℝ³ → ℝ (`EuclideanSpace ℝ (Fin 3)`) that is twice continuously
differentiable on the open unit ball, continuous on the closed unit ball, zero on the unit sphere,
a function of ‖x‖ alone on the closed ball, and solves Δu x + λ e^{u x} = 0 at every x of the open
ball (Δ is Mathlib's Laplacian). The hypotheses of the companion statement are exactly these.

**Not stated here:** λ ≤ 0 (λ = 0 has u = 0; λ < 0 is a different problem); the number of
solutions for each λ; non-radial solutions.

Only Mathlib definitions occur in the statement (no program definition to pin).
-/

namespace Work.Math.GelfandPDEExists
open Set Filter Topology InnerProductSpace Laplacian Metric

/-- Gelfand problem in the unit ball of ℝ³, radial solutions exist: for every λ with
0 < λ ≤ 3.321992118 there is a function u, twice continuously differentiable on the open unit ball,
continuous on the closed unit ball, zero on the unit sphere and a function of ‖x‖ alone on the
closed ball, with Δu + λ eᵘ = 0 at every point of the open ball (Δ is Mathlib's Laplacian). -/
theorem gelfand_pde_radial_exists (lam : ℝ) (hpos : 0 < lam) (hle : lam ≤ 3.321992118) :
    ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
      ContDiffOn ℝ 2 u (ball 0 1) ∧
      ContinuousOn u (closedBall 0 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
      (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0) := by
  sorry

end Work.Math.GelfandPDEExists
