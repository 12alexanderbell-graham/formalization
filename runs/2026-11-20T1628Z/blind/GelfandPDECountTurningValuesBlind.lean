import Mathlib

open Metric Filter
open scoped InnerProductSpace Topology

namespace GelfandBlind

/-- `u` is a radial solution of the Gelfand–Bratu problem `Δu + l e^u = 0` in the unit ball
of `ℝ³` with zero Dirichlet data on the unit sphere. -/
def IsRadialSol (l : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ) : Prop :=
  ContDiffOn ℝ 2 u (ball (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
  ContinuousOn u (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
  (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
  (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1,
    ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, ‖x‖ = ‖y‖ → u x = u y) ∧
  (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + l * Real.exp (u x) = 0)

/-- Number of solutions, identifying solutions that agree on the closed unit ball
(i.e. counting their restrictions to the closed ball). -/
noncomputable def N (l : ℝ) : ℕ∞ :=
  Set.encard ((fun u : EuclideanSpace ℝ (Fin 3) → ℝ =>
      Set.restrict (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) u) ''
    {u | IsRadialSol l u})

theorem blind_gelfand_pde_count_turning_values :
    ∃ lam : ℕ → ℝ,
      (3.321992118 ≤ lam 0 ∧ lam 0 ≤ 3.321992119) ∧
      (1.664155 ≤ lam 1 ∧ lam 1 ≤ 1.664157) ∧
      (2.10852 ≤ lam 2 ∧ lam 2 ≤ 2.10858) ∧
      (1.9637 ≤ lam 3 ∧ lam 3 ≤ 1.9707) ∧
      StrictAnti (fun k : ℕ => lam (2 * k)) ∧
      StrictMono (fun k : ℕ => lam (2 * k + 1)) ∧
      (∀ k : ℕ, lam (2 * k + 1) < 2 ∧ 2 < lam (2 * k)) ∧
      Tendsto lam atTop (𝓝 2) ∧
      (∀ l : ℝ, lam 0 < l → N l = 0) ∧
      N (lam 0) = 1 ∧
      (∀ (k : ℕ) (l : ℝ), lam (2 * k + 2) < l → l < lam (2 * k) →
        N l = ((2 * k + 2 : ℕ) : ℕ∞)) ∧
      (∀ k : ℕ, N (lam (2 * k + 2)) = ((2 * k + 3 : ℕ) : ℕ∞)) ∧
      (∀ l : ℝ, 0 < l → l < lam 1 → N l = 1) ∧
      (∀ k : ℕ, N (lam (2 * k + 1)) = ((2 * k + 2 : ℕ) : ℕ∞)) ∧
      (∀ (k : ℕ) (l : ℝ), lam (2 * k + 1) < l → l < lam (2 * k + 3) →
        N l = ((2 * k + 3 : ℕ) : ℕ∞)) ∧
      N 2 = ⊤ := by
  sorry

end GelfandBlind
