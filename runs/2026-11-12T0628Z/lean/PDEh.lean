import Checked.Trust.NonVacuity
import Checked.Math.GelfandPDE
import Checked.Math.GelfandPDEExists
import Mathlib.Analysis.Complex.ExponentialBounds

open Set Metric InnerProductSpace Laplacian

theorem e2_gt : (3.321992119 : ℝ) < Real.exp 2 := by
  have h := Real.exp_one_gt_d9
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [this]; nlinarith

theorem gelfand_pde_radial_bound_h3 : necessity% Checked.Math.GelfandPDE.gelfand_pde_radial_bound 3 := by
  obtain ⟨u, hu, hc, -, ⟨g, hg⟩, hpde⟩ :=
    Checked.Math.GelfandPDEExists.gelfand_pde_radial_exists 1 one_pos (by norm_num)
  refine ⟨Real.exp 2, fun x => u x - 2, hu.sub contDiffOn_const, hc.sub continuousOn_const,
    ⟨fun r => g r - 2, fun x hx => by simp [hg x hx]⟩, fun x hx => ?_, ?_⟩
  · have hca : ContDiffAt ℝ 2 u x := hu.contDiffAt (isOpen_ball.mem_nhds hx)
    have e : (fun y => u y - 2) = u - fun _ => (2 : ℝ) := rfl
    simp only []
    rw [e, hca.laplacian_sub contDiffAt_const, laplacian_const, Pi.zero_apply, sub_zero]
    have h := hpde x hx
    rw [Real.exp_sub, mul_div_cancel₀ _ (Real.exp_pos 2).ne']
    linarith
  · exact not_le.mpr e2_gt

theorem gelfand_pde_radial_bound_h2 : necessity% Checked.Math.GelfandPDE.gelfand_pde_radial_bound 2 := by
  obtain ⟨u, hu, -, -, ⟨g, hg⟩, hpde⟩ :=
    Checked.Math.GelfandPDEExists.gelfand_pde_radial_exists 1 one_pos (by norm_num)
  set v : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => if ‖x‖ = 1 then 0 else u x - 2 with hv
  have hball : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = u x - 2 := fun x hx => by
    have : ‖x‖ ≠ 1 := (mem_ball_zero_iff.mp hx).ne
    simp [hv, this]
  refine ⟨Real.exp 2, v, (hu.sub contDiffOn_const).congr hball, fun x hx => by simp [hv, hx],
    ⟨fun r => if r = 1 then 0 else g r - 2, fun x hx => ?_⟩, fun x hx => ?_, ?_⟩
  · by_cases h1 : ‖x‖ = 1
    · simp [hv, h1]
    · simp [hv, h1, hg x hx]
  · have hev : v =ᶠ[nhds x] fun y => u y - 2 :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hx) hball
    have hca : ContDiffAt ℝ 2 u x := hu.contDiffAt (isOpen_ball.mem_nhds hx)
    have e : (fun y => u y - 2) = u - fun _ => (2 : ℝ) := rfl
    rw [(laplacian_congr_nhds hev).self_of_nhds, e, hca.laplacian_sub contDiffAt_const, laplacian_const, Pi.zero_apply,
      sub_zero, hball x hx]
    have h := hpde x hx
    rw [Real.exp_sub, mul_div_cancel₀ _ (Real.exp_pos 2).ne']
    linarith
  · exact not_le.mpr e2_gt
