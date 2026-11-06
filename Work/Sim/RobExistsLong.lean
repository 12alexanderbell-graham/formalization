import Mathlib
import Work.Sim.RobExists

/-!
# Robertson's network: long-horizon existence for the clamped reduced field

The clamped field `Work.Sim.RobExists.Φc` is globally Lipschitz (constant 80000) and bounded
(‖Φc p‖ ≤ 50), so Picard–Lindelöf gives a solution on [0, 10^11] from (0, 0), using a ball of
radius 5 · 10^12 ≥ 50 · 10^11.
-/

namespace Work.Sim.RobExistsLong
open Set

theorem exists_clamped_long : ∃ α : ℝ → ℝ × ℝ, α 0 = (0, 0) ∧
    ∀ t ∈ Icc (0 : ℝ) 100000000000,
      HasDerivWithinAt α (Work.Sim.RobExists.Φc (α t)) (Icc 0 100000000000) t := by
  have hPL : IsPicardLindelof (fun _ => Work.Sim.RobExists.Φc) (tmin := 0)
      (tmax := 100000000000) ⟨0, by norm_num, by norm_num⟩ ((0 : ℝ), (0 : ℝ))
      5000000000000 0 50 ⟨80000, by norm_num⟩ :=
    { lipschitzOnWith := fun _ _ => Work.Sim.RobExists.lipΦc.lipschitzOnWith
      continuousOn := fun _ _ => continuousOn_const
      norm_le := fun _ _ p _ => by
        have := Work.Sim.RobExists.normΦc p; exact_mod_cast this
      mul_max_le := by
        simp only [NNReal.coe_ofNat, NNReal.coe_zero, sub_zero]
        norm_num }
  obtain ⟨α, h0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, h0, hα⟩

end Work.Sim.RobExistsLong

#print axioms Work.Sim.RobExistsLong.exists_clamped_long
