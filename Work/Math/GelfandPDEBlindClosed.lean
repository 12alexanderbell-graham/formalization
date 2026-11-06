import Mathlib
import Work.Math.GelfandPDE

/-! Audit of `Work.Math.GelfandPDE.gelfand_pde_radial_bound`: the blind restatement
(`Work.Math.GelfandPDEBlind.no_radial_solution`: radial as "equal norms give equal values" on the
closed ball, conclusion `False` for λ > 3.321992119) proved from the frozen headline; and
non-vacuity of the headline's hypotheses at λ = 0 (u = 0). -/

namespace Work.Math.GelfandPDEBlindClosed
open Laplacian Metric

theorem blind_closed (lam : ℝ) (hlam : 3.321992119 < lam)
    (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hC2 : ContDiffOn ℝ 2 u (ball (0 : EuclideanSpace ℝ (Fin 3)) 1))
    (hcont : ContinuousOn u (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1))
    (hpde : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)
    (hbdry : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (hrad : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1,
            ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, ‖x‖ = ‖y‖ → u x = u y) :
    False := by
  set e : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 1 with he
  have hne : ‖e‖ = 1 := by simp [he]
  have hn : ∀ x : EuclideanSpace ℝ (Fin 3), ‖‖x‖ • e‖ = ‖x‖ := fun x => by
    rw [norm_smul, hne, mul_one, Real.norm_eq_abs, abs_norm]
  have hg : ∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖ :=
    ⟨fun r => u (r • e), fun x hx => hrad x hx _
      (by rw [mem_closedBall_zero_iff, hn]; exact mem_closedBall_zero_iff.1 hx) (hn x).symm⟩
  have := Work.Math.GelfandPDE.gelfand_pde_radial_bound lam u hC2 hcont hbdry hg hpde
  linarith

/-- The hypotheses of the headline can all be met (λ = 0, u = 0); non-vacuity for λ > 0 needs
the existence direction, not yet stated. -/
theorem nonvacuous_zero : ∃ (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ),
    ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
    (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
    (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
    (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0) := by
  refine ⟨0, fun _ => 0, contDiffOn_const, continuousOn_const, fun _ _ => rfl,
    ⟨fun _ => 0, fun _ _ => rfl⟩, fun x _ => ?_⟩
  simp [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]

end Work.Math.GelfandPDEBlindClosed
