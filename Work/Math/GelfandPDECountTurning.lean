import Mathlib
import Work.Math.GelfandPDECountTurningMain

/-! Gelfand problem in the three-dimensional ball as a PDE, `GelfandPDECountTurning`: the exact number of radial
classical solutions for every positive parameter (FROZEN by run 2026-11-18T2228Z before its proof). The parent
headlines `Checked.Math.GelfandPDECount.gelfand_pde_radial_count` and
`Checked.Math.GelfandPDECountValues.gelfand_pde_radial_count_values` count the solutions below the first
minimum of the branch parameter, at the first minimum, at the second maximum and above the second maximum;
here every band is counted: solutions are counted as restrictions to the closed ball (`Set.encard` of the set
of functions on the closed ball that agree there with a radial solution), the band ends are the turning
values of the branch parameter λ(s) = s² e^{W(s)} of the regular isothermal solution W (the first three
enclosed by numbers), and the count is ⊤ at the value two, the limit of the branch parameter.

Planned route (no new certificates): `Checked.Math.BonnorEbertCountMain.count_abstract` applied to the
branch parameter with the turning sequence of `Checked.Math.GelfandExtrema.gelfand_extrema` and the limit
two; the windows of the first two minimum and maximum values from `Checked.Math.GLamBands.bands`; the
solutions for a parameter correspond to the radii with that parameter value (`profile` and the constructions
of `Checked.Math.GelfandPDECountMain`, distinct radii giving distinct centre values), so the restriction map
is a bijection from the radii onto the counted set. -/

namespace Work.Math.GelfandPDECountTurning
open Set Filter Topology InnerProductSpace Laplacian Metric

/-- Gelfand problem in the unit ball of three-dimensional space, number of radial solutions. A radial solution
for the parameter lam is a function u that is twice continuously differentiable on the open unit ball, continuous on
the closed unit ball, zero on the unit sphere and a function of ‖x‖ on the closed ball, with Δu + lam e^u = 0 on
the open ball (Δ is Mathlib's Laplacian); N(lam) is the number of functions g on the closed ball such that
g x = u x on the closed ball for a radial solution u for lam. There is a sequence `lamT` of parameters, with
`lamT 0` between 3.321992118 and 3.321992119, `lamT 1` between 1.664155 and 1.664157 and `lamT 2` between 2.10852
and 2.10858, `lamT (2 * k)` strictly decreasing in k, `lamT (2 * k + 1)` strictly increasing in k,
`lamT (2 * k + 1)` < 2 < `lamT (2 * k)` for every k, and `lamT` tending to 2, such that: N(lam) = 0 for
lam > `lamT 0`; N(`lamT 0`) = 1; for every k, N(lam) = 2k + 2 for `lamT (2 * k + 2)` < lam < `lamT (2 * k)` and
N(`lamT (2 * k + 2)`) = 2k + 3; N(lam) = 1 for 0 < lam < `lamT 1`; for every k, N(`lamT (2 * k + 1)`) = 2k + 2
and N(lam) = 2k + 3 for `lamT (2 * k + 1)` < lam < `lamT (2 * k + 3)`; and N(2) = ⊤. -/
theorem gelfand_pde_radial_count_turning :
    ∃ lamT : ℕ → ℝ,
      3.321992118 ≤ lamT 0 ∧ lamT 0 ≤ 3.321992119 ∧
      1.664155 ≤ lamT 1 ∧ lamT 1 ≤ 1.664157 ∧ 2.10852 ≤ lamT 2 ∧ lamT 2 ≤ 2.10858 ∧
      StrictAnti (fun k : ℕ => lamT (2 * k)) ∧ StrictMono (fun k : ℕ => lamT (2 * k + 1)) ∧
      (∀ k : ℕ, lamT (2 * k + 1) < 2 ∧ 2 < lamT (2 * k)) ∧
      Tendsto lamT atTop (𝓝 2) ∧
      (∀ lam : ℝ, lamT 0 < lam →
        {g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
          (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = h ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)) ∧
          ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}.encard = 0) ∧
      {g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
          (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = h ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lamT 0 * Real.exp (u x) = 0)) ∧
          ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}.encard = 1 ∧
      (∀ k : ℕ, ∀ lam : ℝ, lamT (2 * k + 2) < lam → lam < lamT (2 * k) →
        {g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
          (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = h ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)) ∧
          ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}.encard = ((2 * k + 2 : ℕ) : ℕ∞)) ∧
      (∀ k : ℕ,
        {g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
          (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = h ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lamT (2 * k + 2) * Real.exp (u x) = 0)) ∧
          ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}.encard = ((2 * k + 3 : ℕ) : ℕ∞)) ∧
      (∀ lam : ℝ, 0 < lam → lam < lamT 1 →
        {g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
          (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = h ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)) ∧
          ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}.encard = 1) ∧
      (∀ k : ℕ,
        {g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
          (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = h ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lamT (2 * k + 1) * Real.exp (u x) = 0)) ∧
          ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}.encard = ((2 * k + 2 : ℕ) : ℕ∞)) ∧
      (∀ k : ℕ, ∀ lam : ℝ, lamT (2 * k + 1) < lam → lam < lamT (2 * k + 3) →
        {g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
          (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = h ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)) ∧
          ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}.encard = ((2 * k + 3 : ℕ) : ℕ∞)) ∧
      {g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
          (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = h ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + 2 * Real.exp (u x) = 0)) ∧
          ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}.encard = ⊤ :=
  Work.Math.GelfandPDECountTurningMain.main

end Work.Math.GelfandPDECountTurning
