import Mathlib
import Work.Math.GelfandPDECountTurningValuesFive
import Work.Math.GelfandPDECountTurningValuesFiveBlind

/-! Gelfand problem, number of radial solutions for every positive parameter with the fourth and fifth turning values
enclosed: the blind restatement
`Work.Math.GelfandPDECountTurningValuesFiveBlind.blind_gelfand_pde_count_turning_values_five` (radial as
`‖x‖ = ‖y‖ → u x = u y` for points of norm at most one, solutions counted as the image of the solution set under
restriction to the closed ball) closed from the frozen headline
`Work.Math.GelfandPDECountTurningValuesFive.gelfand_pde_radial_count_turning_values_five`; the statement of
`blind_closed` is the blind statement as written. Adapted by run 2026-11-21T1028Z from
`Work.Math.GelfandPDECountTurningValuesBlindClosed`. -/

namespace Work.Math.GelfandPDECountTurningValuesFiveBlindClosed
open Set Metric Filter Topology InnerProductSpace Laplacian Work.Math.GelfandPDECountTurningValuesFiveBlind

theorem N_eq (lam : ℝ) : N lam =
    {g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
      (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
      (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = h ‖x‖) ∧
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)) ∧
      ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}.encard := by
  unfold N solSet
  congr 1
  ext g
  constructor
  · rintro ⟨u, ⟨h1, h2, h3, h4, h5⟩, rfl⟩
    set e : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 1 with he
    have hne : ‖e‖ = 1 := by simp [he]
    refine ⟨u, ⟨h1, h2, h3, ⟨fun r => u (r • e), fun x hx => ?_⟩, h5⟩, fun x => rfl⟩
    have hx' : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.1 hx
    have hn : ‖‖x‖ • e‖ = ‖x‖ := by rw [norm_smul, hne, mul_one, Real.norm_eq_abs, abs_norm]
    exact h4 x (‖x‖ • e) hx' (by rw [hn]; exact hx') hn.symm
  · rintro ⟨u, ⟨h1, h2, h3, ⟨h, hh⟩, h5⟩, hg⟩
    refine ⟨u, ⟨h1, h2, h3, fun x y hx hy hxy => ?_, h5⟩, funext fun x => (hg x).symm⟩
    rw [hh x (mem_closedBall_zero_iff.2 hx), hh y (mem_closedBall_zero_iff.2 hy), hxy]

theorem blind_closed :
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
  obtain ⟨lam, a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, a7, a8, a9, a10, hA, hB, hC, hD, hE, hF, hG, hH⟩ :=
    Work.Math.GelfandPDECountTurningValuesFive.gelfand_pde_radial_count_turning_values_five
  exact ⟨lam, a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, a7, a8, a9, a10,
    fun l h => (N_eq l).trans (hA l h), (N_eq _).trans hB,
    fun k l h1 h2 => (N_eq l).trans (hC k l h1 h2), fun k => (N_eq _).trans (hD k),
    fun l h1 h2 => (N_eq l).trans (hE l h1 h2), fun k => (N_eq _).trans (hF k),
    fun k l h1 h2 => (N_eq l).trans (hG k l h1 h2), (N_eq 2).trans hH⟩

end Work.Math.GelfandPDECountTurningValuesFiveBlindClosed
