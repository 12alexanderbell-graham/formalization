import Mathlib

/-! Blind restatement of the Gelfand count for every positive parameter with the fourth and fifth turning values
enclosed (run 2026-11-21T1028Z, Sonnet, brief `runs/2026-11-21T1028Z/blind/BRIEF.md`), copied verbatim from
`runs/2026-11-21T1028Z/blind/GelfandPDECountTurningValuesFiveBlind.lean` with the namespace renamed and one compile
repair that keeps its meaning: `InnerProductSpace.laplacian u x` (no such Mathlib name) written `Δ u x` with
`open Laplacian`, so that it is Mathlib's Laplacian (the brief's Δ), as in run 2026-11-20T1628Z. -/

open InnerProductSpace Laplacian

namespace Work.Math.GelfandPDECountTurningValuesFiveBlind

/-- Radial solution of Δu + λ e^u = 0 in the unit ball of ℝ³, u = 0 on the sphere. -/
def IsRadialSol (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ) : Prop :=
  ContDiffOn ℝ 2 u (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
  ContinuousOn u (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
  (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
  (∀ x y : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖x‖ = ‖y‖ → u x = u y) ∧
  (∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1,
    Δ u x + lam * Real.exp (u x) = 0)

/-- Solutions identified when they agree on the closed unit ball: restrict to the closed ball. -/
def solSet (lam : ℝ) : Set (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ) :=
  (fun u => fun x => u x.1) '' {u | IsRadialSol lam u}

/-- Number of distinct radial solutions, in `ℕ∞` (`⊤` if infinite). -/
noncomputable def N (lam : ℝ) : ℕ∞ := (solSet lam).encard

theorem blind_gelfand_pde_count_turning_values_five :
    ∃ l : ℕ → ℝ,
      3.321992118 ≤ l 0 ∧ l 0 ≤ 3.321992119 ∧
      1.664155 ≤ l 1 ∧ l 1 ≤ 1.664157 ∧
      2.10852 ≤ l 2 ∧ l 2 ≤ 2.10858 ∧
      1.967422 ≤ l 3 ∧ l 3 ≤ 1.967510 ∧
      2.009926 ≤ l 4 ∧ l 4 ≤ 2.010028 ∧
      StrictAnti (fun k => l (2 * k)) ∧
      StrictMono (fun k => l (2 * k + 1)) ∧
      (∀ k, l (2 * k + 1) < 2 ∧ 2 < l (2 * k)) ∧
      Filter.Tendsto l Filter.atTop (nhds 2) ∧
      (∀ lam : ℝ, l 0 < lam → N lam = 0) ∧
      N (l 0) = 1 ∧
      (∀ k : ℕ, ∀ lam : ℝ, l (2 * k + 2) < lam → lam < l (2 * k) →
        N lam = ((2 * k + 2 : ℕ) : ℕ∞)) ∧
      (∀ k : ℕ, N (l (2 * k + 2)) = ((2 * k + 3 : ℕ) : ℕ∞)) ∧
      (∀ lam : ℝ, 0 < lam → lam < l 1 → N lam = 1) ∧
      (∀ k : ℕ, N (l (2 * k + 1)) = ((2 * k + 2 : ℕ) : ℕ∞)) ∧
      (∀ k : ℕ, ∀ lam : ℝ, l (2 * k + 1) < lam → lam < l (2 * k + 3) →
        N lam = ((2 * k + 3 : ℕ) : ℕ∞)) ∧
      N 2 = ⊤ := by
  sorry

end Work.Math.GelfandPDECountTurningValuesFiveBlind
