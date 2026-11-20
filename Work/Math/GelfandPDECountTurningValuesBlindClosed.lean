import Mathlib
import Work.Math.GelfandPDECountTurningValues
import Work.Math.GelfandPDECountTurningValuesBlind

/-! Gelfand problem, number of radial solutions for every positive parameter with the fourth turning value enclosed: the blind restatement
`Work.Math.GelfandPDECountTurningValuesBlind.blind_gelfand_pde_count_turning_values` (radial as `‖x‖ = ‖y‖ → u x = u y` on
the closed ball, solutions counted as the image of the solution set under restriction to the closed ball)
closed from the frozen headline `Work.Math.GelfandPDECountTurningValues.gelfand_pde_radial_count_turning_values`. Adapted
by run 2026-11-20T1628Z from `Work.Math.GelfandPDECountTurningBlindClosed`. -/

namespace Work.Math.GelfandPDECountTurningValuesBlindClosed
open Set Metric Filter Topology InnerProductSpace Laplacian Work.Math.GelfandPDECountTurningValuesBlind

theorem N_eq (lam : ℝ) : N lam =
    {g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
      (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
      (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = h ‖x‖) ∧
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)) ∧
      ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}.encard := by
  unfold N
  congr 1
  ext g
  constructor
  · rintro ⟨u, ⟨h1, h2, h3, h4, h5⟩, rfl⟩
    set e : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 1 with he
    have hne : ‖e‖ = 1 := by simp [he]
    refine ⟨u, ⟨h1, h2, h3, ⟨fun r => u (r • e), fun x hx => ?_⟩, h5⟩, fun x => rfl⟩
    have hx' : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.1 hx
    have hn : ‖‖x‖ • e‖ = ‖x‖ := by rw [norm_smul, hne, mul_one, Real.norm_eq_abs, abs_norm]
    exact h4 x hx (‖x‖ • e) (mem_closedBall_zero_iff.2 (by rw [hn]; exact hx')) hn.symm
  · rintro ⟨u, ⟨h1, h2, h3, ⟨h, hh⟩, h5⟩, hg⟩
    refine ⟨u, ⟨h1, h2, h3, fun x hx y hy hxy => ?_, h5⟩, funext fun x => (hg x).symm⟩
    rw [hh x hx, hh y hy, hxy]

theorem blind_closed :
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
  obtain ⟨lam, a1, a2, a3, a4, a5, a6, b1, b2, a7, a8, a9, a10, hA, hB, hC, hD, hE, hF, hG, hH⟩ :=
    Work.Math.GelfandPDECountTurningValues.gelfand_pde_radial_count_turning_values
  exact ⟨lam, ⟨a1, a2⟩, ⟨a3, a4⟩, ⟨a5, a6⟩, ⟨b1, b2⟩, a7, a8, a9, a10,
    fun l h => (N_eq l).trans (hA l h), (N_eq _).trans hB,
    fun k l h1 h2 => (N_eq l).trans (hC k l h1 h2), fun k => (N_eq _).trans (hD k),
    fun l h1 h2 => (N_eq l).trans (hE l h1 h2), fun k => (N_eq _).trans (hF k),
    fun k l h1 h2 => (N_eq l).trans (hG k l h1 h2), (N_eq 2).trans hH⟩

end Work.Math.GelfandPDECountTurningValuesBlindClosed
