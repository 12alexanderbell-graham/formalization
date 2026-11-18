import Mathlib

/-! Blind restatement of the Gelfand count for every positive parameter (run 2026-11-18T2228Z, Sonnet, brief
`runs/2026-11-18T2228Z/blind/BRIEF.md`), copied verbatim from
`runs/2026-11-18T2228Z/blind/GelfandPDECountTurningBlind.lean` with the namespace renamed and one compile repair that keeps its meaning (the same as run
2026-11-18T1028Z's): `InnerProductSpace.laplacian u x` (not a Mathlib name) written `Δ u x` under
`open Laplacian` (Mathlib's Laplacian, the brief's Δ). -/

open Metric Filter Topology Laplacian

namespace Work.Math.GelfandPDECountTurningBlind

/-- Euclidean 3-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- `u` is a radial solution of the Gelfand–Bratu problem `Δu + λ e^u = 0` in the unit ball
of `ℝ³` with zero Dirichlet data on the unit sphere. -/
def IsRadialSolution (lam : ℝ) (u : E3 → ℝ) : Prop :=
  ContDiffOn ℝ 2 u (ball (0 : E3) 1) ∧
  ContinuousOn u (closedBall (0 : E3) 1) ∧
  (∀ x : E3, ‖x‖ = 1 → u x = 0) ∧
  (∀ x ∈ closedBall (0 : E3) 1, ∀ y ∈ closedBall (0 : E3) 1, ‖x‖ = ‖y‖ → u x = u y) ∧
  (∀ x ∈ ball (0 : E3) 1, Δ u x + lam * Real.exp (u x) = 0)

/-- Number of radial solutions, identifying two solutions that agree on the closed unit ball
(values in `ℕ∞`, so `⊤` means infinitely many). -/
noncomputable def N (lam : ℝ) : ℕ∞ :=
  ((fun u : E3 → ℝ => (closedBall (0 : E3) 1).restrict u) ''
    {u : E3 → ℝ | IsRadialSolution lam u}).encard

theorem blind_gelfand_pde_count_turning :
    ∃ l : ℕ → ℝ,
      (3.321992118 ≤ l 0 ∧ l 0 ≤ 3.321992119) ∧
      (1.664155 ≤ l 1 ∧ l 1 ≤ 1.664157) ∧
      (2.10852 ≤ l 2 ∧ l 2 ≤ 2.10858) ∧
      StrictAnti (fun k : ℕ => l (2 * k)) ∧
      StrictMono (fun k : ℕ => l (2 * k + 1)) ∧
      (∀ k : ℕ, l (2 * k + 1) < 2 ∧ 2 < l (2 * k)) ∧
      Tendsto l atTop (𝓝 2) ∧
      (∀ lam : ℝ, l 0 < lam → N lam = 0) ∧
      N (l 0) = 1 ∧
      (∀ (k : ℕ) (lam : ℝ), l (2 * k + 2) < lam → lam < l (2 * k) →
        N lam = ((2 * k + 2 : ℕ) : ℕ∞)) ∧
      (∀ k : ℕ, N (l (2 * k + 2)) = ((2 * k + 3 : ℕ) : ℕ∞)) ∧
      (∀ lam : ℝ, 0 < lam → lam < l 1 → N lam = 1) ∧
      (∀ k : ℕ, N (l (2 * k + 1)) = ((2 * k + 2 : ℕ) : ℕ∞)) ∧
      (∀ (k : ℕ) (lam : ℝ), l (2 * k + 1) < lam → lam < l (2 * k + 3) →
        N lam = ((2 * k + 3 : ℕ) : ℕ∞)) ∧
      N 2 = ⊤ := by
  sorry

end Work.Math.GelfandPDECountTurningBlind
