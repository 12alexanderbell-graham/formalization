import Mathlib
import Checked.Math.GelfandPDECountTurningMain
import Checked.Math.GelfandTurningValuesFive

/-! Gelfand problem in the three-dimensional ball as a PDE, `GelfandPDECountTurningValuesFive`: the number of radial
classical solutions for every positive parameter, as in `Checked.Math.GelfandPDECountTurning`, with the value of the
branch parameter at its fourth and fifth turning points enclosed as well (FROZEN by run 2026-11-21T1028Z before its proof). The
route will be `Checked.Math.GelfandPDECountTurningMain.cset_encard` and
`Checked.Math.BonnorEbertCountMain.count_abstract` applied to the turning sequence of
`Checked.Math.GelfandTurningValuesFive.gelfand_turning_values_five`. -/

namespace Work.Math.GelfandPDECountTurningValuesFive
open Set Filter Topology InnerProductSpace Laplacian Metric

/-- Gelfand problem in the unit ball of three-dimensional space, number of radial solutions. A radial solution
for the parameter lam is a function u that is twice continuously differentiable on the open unit ball, continuous on
the closed unit ball, zero on the unit sphere and a function of ‖x‖ on the closed ball, with Δu + lam e^u = 0 on
the open ball (Δ is Mathlib's Laplacian); N(lam) is the number of functions g on the closed ball such that
g x = u x on the closed ball for a radial solution u for lam. There is a sequence `lamT` of parameters, with
`lamT 0` between 3.321992118 and 3.321992119, `lamT 1` between 1.664155 and 1.664157 and `lamT 2` between 2.10852
and 2.10858, `lamT 3` between 1.967422 and 1.967510, `lamT 4` between 2.009926 and 2.010028, `lamT (2 * k)` strictly decreasing in k, `lamT (2 * k + 1)`
strictly increasing in k,
`lamT (2 * k + 1)` < 2 < `lamT (2 * k)` for every k, and `lamT` tending to 2, such that: N(lam) = 0 for
lam > `lamT 0`; N(`lamT 0`) = 1; for every k, N(lam) = 2k + 2 for `lamT (2 * k + 2)` < lam < `lamT (2 * k)` and
N(`lamT (2 * k + 2)`) = 2k + 3; N(lam) = 1 for 0 < lam < `lamT 1`; for every k, N(`lamT (2 * k + 1)`) = 2k + 2
and N(lam) = 2k + 3 for `lamT (2 * k + 1)` < lam < `lamT (2 * k + 3)`; and N(2) = ⊤. -/
theorem gelfand_pde_radial_count_turning_values_five :
    ∃ lamT : ℕ → ℝ,
      3.321992118 ≤ lamT 0 ∧ lamT 0 ≤ 3.321992119 ∧
      1.664155 ≤ lamT 1 ∧ lamT 1 ≤ 1.664157 ∧ 2.10852 ≤ lamT 2 ∧ lamT 2 ≤ 2.10858 ∧
      1.967422 ≤ lamT 3 ∧ lamT 3 ≤ 1.967510 ∧ 2.009926 ≤ lamT 4 ∧ lamT 4 ≤ 2.010028 ∧
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
          ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}.encard = ⊤ := by
  sorry

end Work.Math.GelfandPDECountTurningValuesFive
