import Mathlib

/-! Gelfand problem in the three-dimensional ball as a PDE, `GelfandPDEMany` (FROZEN by run
2026-11-15T1828Z before proof).

Same PDE and solution class as `Checked/Math/GelfandPDE.lean` (headline `gelfand_pde_radial_bound`) and
`Checked/Math/GelfandPDEExists.lean` (headline `gelfand_pde_radial_exists`): u twice continuously
differentiable on the open unit ball of ℝ³ (`EuclideanSpace ℝ (Fin 3)`), continuous on the closed ball, zero
on the unit sphere, a function of ‖x‖ on the closed ball, and Δu + λ eᵘ = 0 on the open ball (Δ is Mathlib's
Laplacian).

What this adds: `gelfand_pde_radial_exists` gives one radial solution for 0 < λ ≤ 3.321992118 and
`gelfand_pde_radial_bound` none above 3.321992119. This statement gives the multiplicity of radial
solutions (Joseph and Lundgren 1973 for dimensions 3 to 9, stated here for dimension 3): (i) for λ = 2
there are infinitely many pairwise distinct radial solutions (an injective sequence); (ii) for every N
there is ε > 0 such that every λ with |λ − 2| < ε has at least N pairwise distinct radial solutions;
(iii) every λ with 2 ≤ λ < 3.321992118 has at least two distinct radial solutions.

Route (planned, no new certificates): take the global regular solution W of w'' + (2/s) w' + e^w = 0,
w(0) = 0 (`Checked.Math.BEGlobalExists.exists_global`); for every s > 0 with s² e^{W(s)} = λ the function
u(x) = W(s‖x‖) + log(s²/λ) is a radial solution for λ (the construction in the proof of
`gelfand_pde_radial_exists`, there for s < 41/10 only), and its value at the centre is log(s²/λ), so
distinct s give distinct u. The radii come from `Checked.Math.GelfandExtrema.gelfand_extrema` by the
intermediate value theorem: λ(s) = s² e^{W(s)} takes every value strictly between λ(ζ(k)) and λ(ζ(k+1))
on (ζ(k), ζ(k+1)), and these values straddle 2 (maxima above 2, minima below 2); for (ii) take ε below
every |λ(ζ(k)) − 2|, k ≤ N, and below 1; for (iii) one radius in (0, ζ(0)) and one in (ζ(0), ζ(1)). -/

namespace Work.Math.GelfandPDEMany
open Set Filter Topology InnerProductSpace Laplacian Metric

/-- Gelfand problem in the unit ball of three-dimensional space, multiplicity of radial solutions:
infinitely many for λ = 2, at least N for λ close enough to 2, at least two for 2 ≤ λ < 3.321992118. -/
theorem gelfand_pde_radial_many :
    (∃ u : ℕ → EuclideanSpace ℝ (Fin 3) → ℝ, Function.Injective u ∧ ∀ i : ℕ,
      ContDiffOn ℝ 2 (u i) (ball 0 1) ∧
      ContinuousOn (u i) (closedBall 0 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u i x = 0) ∧
      (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u i x = g ‖x‖) ∧
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ (u i) x + 2 * Real.exp (u i x) = 0)) ∧
    (∀ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ lam : ℝ, |lam - 2| < ε →
      ∃ u : Fin N → EuclideanSpace ℝ (Fin 3) → ℝ, Function.Injective u ∧ ∀ i : Fin N,
        ContDiffOn ℝ 2 (u i) (ball 0 1) ∧
        ContinuousOn (u i) (closedBall 0 1) ∧
        (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u i x = 0) ∧
        (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u i x = g ‖x‖) ∧
        (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ (u i) x + lam * Real.exp (u i x) = 0)) ∧
    (∀ lam : ℝ, 2 ≤ lam → lam < 3.321992118 →
      ∃ u v : EuclideanSpace ℝ (Fin 3) → ℝ, u ≠ v ∧
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

end Work.Math.GelfandPDEMany
