import Checked.Trust.NonVacuity
import Checked.Trust.NecessityM
import Checked.Math.GelfandPDEBound

/-! Hypothesis necessity for `Checked.Math.GelfandPDEBound.gelfand_pde_bound` (run 2026-11-20T2228Z): continuity
on the closed ball, the boundary condition and the equation are needed. The counter-examples are those of
`Checked.Trust.NecessityM` and `Checked.Trust.NecessityB` for the radial statement, with its radial hypothesis left
out: the shift u − 2 of the solution for the parameter one, which solves the equation with the parameter e² (above
the bound), either with boundary value −2 or set to zero on the unit sphere; and the zero function with the
parameter four when the equation is dropped. Module `NecessityBH`. -/

namespace Checked.Trust.NecessityBH
open Set Filter Topology Metric InnerProductSpace Laplacian

/-- Continuity on the closed ball is needed in `gelfand_pde_bound`. -/
theorem gelfand_pde_bound_h2 : necessity% Checked.Math.GelfandPDEBound.gelfand_pde_bound 2 := by
  obtain ⟨u, hu, -, -, -, hpde⟩ :=
    Checked.Math.GelfandPDEExists.gelfand_pde_radial_exists 1 one_pos (by norm_num)
  set v : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => if ‖x‖ = 1 then 0 else u x - 2 with hv
  have hball : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = u x - 2 := fun x hx => by
    have : ‖x‖ ≠ 1 := (mem_ball_zero_iff.mp hx).ne
    simp [hv, this]
  refine ⟨Real.exp 2, v, (hu.sub contDiffOn_const).congr hball, fun x hx => by simp [hv, hx],
    fun x hx => ?_, ?_⟩
  · have hev : v =ᶠ[nhds x] fun y => u y - 2 :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hx) hball
    have hca : ContDiffAt ℝ 2 u x := hu.contDiffAt (isOpen_ball.mem_nhds hx)
    have e : (fun y => u y - 2) = u - fun _ => (2 : ℝ) := rfl
    rw [(laplacian_congr_nhds hev).self_of_nhds, e, hca.laplacian_sub contDiffAt_const, laplacian_const,
      Pi.zero_apply, sub_zero, hball x hx]
    have h := hpde x hx
    rw [Real.exp_sub, mul_div_cancel₀ _ (Real.exp_pos 2).ne']
    linarith
  · exact not_le.mpr Checked.Trust.NecessityM.e2_gt

/-- The boundary condition is needed in `gelfand_pde_bound`. -/
theorem gelfand_pde_bound_h3 : necessity% Checked.Math.GelfandPDEBound.gelfand_pde_bound 3 := by
  obtain ⟨u, hu, hc, -, -, hpde⟩ :=
    Checked.Math.GelfandPDEExists.gelfand_pde_radial_exists 1 one_pos (by norm_num)
  refine ⟨Real.exp 2, fun x => u x - 2, hu.sub contDiffOn_const, hc.sub continuousOn_const,
    fun x hx => ?_, ?_⟩
  · have hca : ContDiffAt ℝ 2 u x := hu.contDiffAt (isOpen_ball.mem_nhds hx)
    have e : (fun y => u y - 2) = u - fun _ => (2 : ℝ) := rfl
    simp only []
    rw [e, hca.laplacian_sub contDiffAt_const, laplacian_const, Pi.zero_apply, sub_zero]
    have h := hpde x hx
    rw [Real.exp_sub, mul_div_cancel₀ _ (Real.exp_pos 2).ne']
    linarith
  · exact not_le.mpr Checked.Trust.NecessityM.e2_gt

/-- The equation is needed in `gelfand_pde_bound`: the zero function meets every other hypothesis with the
parameter four. -/
theorem gelfand_pde_bound_h4 : necessity% Checked.Math.GelfandPDEBound.gelfand_pde_bound 4 := by
  refine ⟨4, fun _ => 0, contDiffOn_const, continuousOn_const, fun _ _ => rfl, by norm_num⟩

end Checked.Trust.NecessityBH
