import Checked.Trust.NonVacuity
import Checked.Trust.NecessityM
import Checked.Trust.NecessityZ
import Checked.Math.BonnorEbertMin2
import Checked.Math.BonnorEbertMax
import Checked.Math.GelfandExists
import Mathlib.Analysis.Real.Pi.Bounds

/-! Hypothesis necessity for the second minimum of the Bonnor–Ebert mass
(`Checked.Math.BonnorEbertMin2.bonnor_ebert_second_min`, run 2026-11-14T1428Z; adapted from
`Checked.Trust.NecessityAE` for the second maximum). Hypotheses as numbered in
`CLAIMS.md`: 1 the length of the interval, 2 the derivative of w, 3 continuity of φ at the centre, 4 the
equation, 5 the centre value w(0) = 0. The witnesses are those of `Checked.Trust.NecessityZ` for the maximum:
the zero function (1, 4) has mass zero at the second minimiser, w = 0 with a linear φ (2) has a mass far
above the window there; continuity of φ at the centre is forced by the equation (3); and the scaling symmetry of the
isothermal equation (5) turns a solution on twice the interval into one whose maximiser sits at half the
true critical radius. -/

namespace Checked.Trust.NecessityAF
open Set

theorem bonnor_ebert_second_min_r3 : dropped% Checked.Math.BonnorEbertMin2.bonnor_ebert_second_min 3 := by
  intro S hS w φ h1 h3 h4
  refine Checked.Math.BonnorEbertMin2.bonnor_ebert_second_min S hS w φ h1 ?_ h3 h4
  exact Checked.Trust.NCB.cont_at_zero_of_continuous S (by linarith) 1 w φ (fun y => -Real.exp y)
    (by fun_prop) h1 (fun ξ hξ => (h3 ξ hξ).congr_deriv (by push_cast; ring))

theorem bonnor_ebert_second_min_h1 : necessity% Checked.Math.BonnorEbertMin2.bonnor_ebert_second_min 1 := by
  refine ⟨0, fun _ => 0, fun _ => 0, fun s _ => hasDerivWithinAt_const _ _ _,
    continuousWithinAt_const, fun s hs => absurd hs (by simp), rfl, ?_⟩
  rintro ⟨ξ₁, ξ₂, ξ₃, ξ₄, -, -, -, -, -, -, -, -, -, -, -, -, h10, -⟩
  simp at h10
  norm_num at h10

theorem bonnor_ebert_second_min_h4 : necessity% Checked.Math.BonnorEbertMin2.bonnor_ebert_second_min 4 := by
  refine ⟨20000, le_rfl, fun _ => 0, fun _ => 0, fun s _ => hasDerivWithinAt_const _ _ _,
    continuousWithinAt_const, rfl, ?_⟩
  rintro ⟨ξ₁, ξ₂, ξ₃, ξ₄, -, -, -, -, -, -, -, -, -, -, -, -, h10, -⟩
  simp at h10
  norm_num at h10

theorem bonnor_ebert_second_min_h2 : necessity% Checked.Math.BonnorEbertMin2.bonnor_ebert_second_min 2 := by
  refine ⟨20000, le_rfl, fun _ => 0, fun s => -(s / 3), (continuous_id.div_const 3).neg.continuousWithinAt,
    fun s hs => ?_, rfl, ?_⟩
  · have hs0 : s ≠ 0 := (mem_Ioc.mp hs).1.ne'
    exact (((hasDerivAt_id' s).div_const 3).neg.hasDerivWithinAt).congr_deriv
      (by rw [Real.exp_zero]; field_simp; ring)
  · rintro ⟨ξ₁, ξ₂, ξ₃, ξ₄, -, -, -, -, -, -, hlo, -, -, -, -, -, -, h6, -⟩
    have hsq : Real.sqrt (4 * Real.pi) ≤ 4 := by
      rw [Real.sqrt_le_left (by norm_num)]
      nlinarith [Real.pi_lt_d2]
    have hsq0 : 0 < Real.sqrt (4 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    simp only [neg_neg, zero_div, Real.exp_zero, mul_one] at h6
    rw [div_le_iff₀ hsq0] at h6
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 0.787995)]

theorem bonnor_ebert_second_min_h5 : necessity% Checked.Math.BonnorEbertMin2.bonnor_ebert_second_min 5 := by
  obtain ⟨w, φ, hw, hφ0, hφ, h0⟩ := Checked.Math.GelfandExists.exists_solution (2 * 20000) (by norm_num)
  obtain ⟨hu, hψ0, hψ⟩ := Checked.Trust.NecessityM.scaled_hyps 2 20000 (by norm_num) w φ hw hφ0 hφ
  refine ⟨20000, le_rfl, fun s => w (2 * s) + 2 * Real.log 2, fun s => 2 * φ (2 * s), hu, hψ0, hψ, ?_⟩
  rintro ⟨η, -, -, -, hη1, hη2, -, -, -, -, -, -, hglob, -⟩
  obtain ⟨ξ, hξ1, hξ2, hmax, -, -⟩ :=
    Checked.Math.BonnorEbertMax.bonnor_ebert_max (2 * 20000) (by norm_num) w φ hw hφ0 hφ h0
  have hm : ∀ s, (fun s => s ^ 2 * (-(fun s => 2 * φ (2 * s)) s) *
      Real.exp ((fun s => w (2 * s) + 2 * Real.log 2) s / 2) / Real.sqrt (4 * Real.pi)) s =
      Checked.Trust.NecessityM.mass w φ (2 * s) := by
    intro s
    simp only [Checked.Trust.NecessityM.mass]
    rw [show (w (2 * s) + 2 * Real.log 2) / 2 = w (2 * s) / 2 + Real.log 2 by ring, Real.exp_add,
      Real.exp_log (by norm_num)]
    ring
  have h1 := hglob (ξ / 2) ⟨by linarith, by linarith⟩ (by intro h; linarith)
  have h2 := hmax (2 * η) ⟨by linarith, by linarith⟩ (by intro h; linarith)
  have e1 := hm (ξ / 2)
  have e2 := hm η
  simp only at e1 e2 h1
  rw [e1, e2, show 2 * (ξ / 2) = ξ by ring] at h1
  simp only [Checked.Trust.NecessityM.mass] at h1
  linarith

end Checked.Trust.NecessityAF
