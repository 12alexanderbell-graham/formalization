import Checked.Trust.NecessityAJ
import Checked.Math.GelfandExtrema

/-! Hypothesis necessity for the turning points of the radial Gelfand branch
(`Checked.Math.GelfandExtrema.gelfand_extrema`, run 2026-11-15T1228Z). The hypotheses are those of
`Checked.Math.BonnorEbertExtrema.bonnor_ebert_extrema` in the same order, and the witnesses of
`Checked.Trust.NecessityAJ` carry over: w = 0 with a linear φ (1) and the zero function (3) have the branch
parameter s², which increases without bound, so no radius is its strict maximum; continuity of φ at the centre
is forced by the equation (2 REDUNDANT); and the scaling symmetry of the equation (4), which leaves the branch
parameter invariant up to the change of radius s ↦ 2s, moves the strict maximiser to half the true radius. -/

namespace Checked.Trust.NecessityAO
open Set Filter Topology

theorem gelfand_extrema_r2 :
    dropped% Checked.Math.GelfandExtrema.gelfand_extrema 2 := by
  intro w φ h1 h3 h4
  exact Checked.Math.GelfandExtrema.gelfand_extrema w φ h1
    (Checked.Trust.NecessityAJ.cont_at_zero_Ici w φ h1 h3) h3 h4

theorem gelfand_extrema_h3 :
    necessity% Checked.Math.GelfandExtrema.gelfand_extrema 3 := by
  refine ⟨fun _ => 0, fun _ => 0, fun s _ => hasDerivWithinAt_const _ _ _,
    continuousWithinAt_const, rfl, ?_⟩
  rintro ⟨ζ, -, -, h0, -, -, -, hmax, -⟩
  have h := hmax (ζ 0 + 1) (by simp only [mem_Ici]; linarith) (by intro h; linarith)
  simp only [Real.exp_zero, mul_one] at h
  nlinarith

theorem gelfand_extrema_h1 :
    necessity% Checked.Math.GelfandExtrema.gelfand_extrema 1 := by
  refine ⟨fun _ => 0, fun s => -(s / 3), (continuous_id.div_const 3).neg.continuousWithinAt,
    fun s hs => ?_, rfl, ?_⟩
  · have hs0 : s ≠ 0 := (mem_Ioi.mp hs).ne'
    exact (((hasDerivAt_id' s).div_const 3).neg.hasDerivWithinAt).congr_deriv
      (by rw [Real.exp_zero]; field_simp; ring)
  · rintro ⟨ζ, -, -, h0, -, -, -, hmax, -⟩
    have h := hmax (ζ 0 + 1) (by simp only [mem_Ici]; linarith) (by intro h; linarith)
    simp only [Real.exp_zero, mul_one] at h
    nlinarith

theorem gelfand_extrema_h4 :
    necessity% Checked.Math.GelfandExtrema.gelfand_extrema 4 := by
  obtain ⟨w, φ, hw, hφ0, hφ, h0⟩ := Checked.Math.BEGlobalExists.exists_global
  obtain ⟨hu, hψ0, hψ⟩ := Checked.Trust.NecessityAJ.scaled_hyps_Ici 2 (by norm_num) w φ hw hφ0 hφ
  refine ⟨fun s => w (2 * s) + 2 * Real.log 2, fun s => 2 * φ (2 * s), hu, hψ0, hψ, ?_⟩
  rintro ⟨η, -, -, hη1, -, -, -, hglob, -⟩
  obtain ⟨ζ, -, -, hζ1, hζ2, -, -, hmax, -⟩ :=
    Checked.Math.GelfandExtrema.gelfand_extrema w φ hw hφ0 hφ h0
  have hl : ∀ s, s ^ 2 * Real.exp ((fun s => w (2 * s) + 2 * Real.log 2) s) =
      (2 * s) ^ 2 * Real.exp (w (2 * s)) := by
    intro s
    simp only
    rw [Real.exp_add, show 2 * Real.log 2 = Real.log (2 ^ 2) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by norm_num)]
    ring
  have h1 := hglob (ζ 0 / 2) (by simp only [mem_Ici]; linarith) (by intro h; linarith)
  have h2 := hmax (2 * η 0) (by simp only [mem_Ici]; linarith) (by intro h; linarith)
  rw [hl, hl, show 2 * (ζ 0 / 2) = ζ 0 by ring] at h1
  linarith

end Checked.Trust.NecessityAO
