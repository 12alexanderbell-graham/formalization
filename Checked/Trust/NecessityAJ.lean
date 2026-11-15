import Checked.Trust.NonVacuity
import Checked.Trust.NecessityB
import Checked.Trust.NecessityM
import Checked.Math.BonnorEbertExtrema
import Checked.Math.BEGlobalExists
import Mathlib.Analysis.Real.Pi.Bounds

/-! Hypothesis necessity for every extremum of the Bonnor–Ebert mass
(`Checked.Math.BonnorEbertExtrema.bonnor_ebert_extrema`, run 2026-11-15T0228Z; adapted from
`Checked.Trust.NecessityAG` for the third maximum). Hypotheses as numbered in `CLAIMS.md`: 1 the derivative
of w, 2 continuity of φ at the centre, 3 the equation, 4 the centre value w(0) = 0. The witnesses: w = 0 with
a linear φ (1) has a mass that increases without bound, so no radius is its strict maximum; continuity of φ at
the centre is forced by the equation (2); the zero function (3) has mass zero everywhere, so no radius is its
strict maximum; and the scaling symmetry of the isothermal equation (4) turns the regular solution on the
half-line into one whose strict maximiser sits at half the true critical radius. -/

namespace Checked.Trust.NecessityAJ
open Set Filter Topology

/-- Scaling symmetry of the isothermal equation on the half-line: if w solves it on [0, ∞) and c > 0, then
u(s) = w(cs) + 2 log c, with derivative c φ(cs), solves it on [0, ∞). -/
theorem scaled_hyps_Ici (c : ℝ) (hc : 0 < c) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt w (φ s) (Ici 0) s)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (hφ : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s) :
    (∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => w (c * s) + 2 * Real.log c)
        ((fun s => c * φ (c * s)) s) (Ici 0) s) ∧
    ContinuousWithinAt (fun s => c * φ (c * s)) (Ici 0) 0 ∧
    (∀ s ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun s => c * φ (c * s))
        (-(2 / s * (fun s => c * φ (c * s)) s) - Real.exp ((fun s => w (c * s) + 2 * Real.log c) s))
        (Ici 0) s) := by
  have hmaps : MapsTo (fun s : ℝ => c * s) (Ici 0) (Ici 0) := by
    intro s hs
    exact mul_nonneg hc.le hs
  have hlin : ∀ s : ℝ, HasDerivWithinAt (fun s : ℝ => c * s) c (Ici 0) s := fun s => by
    simpa using ((hasDerivAt_id s).const_mul c).hasDerivWithinAt
  have hlog : Real.exp (2 * Real.log c) = c ^ 2 := by
    rw [show (2 : ℝ) * Real.log c = Real.log (c ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
  refine ⟨fun s hs => ?_, ?_, fun s hs => ?_⟩
  · have h := ((hw (c * s) (hmaps hs)).scomp s (hlin s) hmaps).add_const (2 * Real.log c)
    refine h.congr_deriv ?_
    simp [smul_eq_mul]
  · have hcc : ContinuousWithinAt (fun s : ℝ => c * s) (Ici 0) 0 :=
      (continuous_const.mul continuous_id).continuousWithinAt
    have h := ContinuousWithinAt.comp (g := φ) (f := fun s : ℝ => c * s) (x := 0)
      (by simpa using hφ0) hcc hmaps
    exact (continuousWithinAt_const (b := c)).mul h
  · have hs' : c * s ∈ Ioi (0 : ℝ) := mul_pos hc hs
    have h := ((hφ (c * s) hs').scomp s (hlin s) hmaps).const_mul c
    refine h.congr_deriv ?_
    have hs0 : s ≠ 0 := (mem_Ioi.mp hs).ne'
    have hc0 : c ≠ 0 := hc.ne'
    simp only [smul_eq_mul, Real.exp_add, hlog]
    field_simp

/-- Continuity of φ at the centre within the half-line follows from the equation and the derivative of w. -/
theorem cont_at_zero_Ici (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt w (φ s) (Ici 0) s)
    (hφ : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s) :
    ContinuousWithinAt φ (Ici 0) 0 := by
  have h1 : ∀ ξ ∈ Icc (0 : ℝ) 1, HasDerivWithinAt w (φ ξ) (Icc 0 1) ξ := fun ξ hξ =>
    (hw ξ hξ.1).mono Icc_subset_Ici_self
  have h3 : ∀ ξ ∈ Ioc (0 : ℝ) 1, HasDerivWithinAt φ
      (-((((1 : ℕ) : ℝ) + 1) / ξ * φ ξ) + (fun y => -Real.exp y) (w ξ)) (Icc 0 1) ξ := fun ξ hξ =>
    ((hφ ξ hξ.1).mono Icc_subset_Ici_self).congr_deriv (by push_cast; ring)
  have hc := Checked.Trust.NCB.cont_at_zero_of_continuous 1 one_pos 1 w φ (fun y => -Real.exp y)
    (by fun_prop) h1 h3
  have hmem : Icc (0 : ℝ) 1 ∈ 𝓝[Ici 0] 0 := by
    rw [show Icc (0 : ℝ) 1 = Ici 0 ∩ Iic 1 by ext; simp]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds one_pos)
  exact hc.mono_of_mem_nhdsWithin hmem

theorem bonnor_ebert_extrema_r2 :
    dropped% Checked.Math.BonnorEbertExtrema.bonnor_ebert_extrema 2 := by
  intro w φ h1 h3 h4
  exact Checked.Math.BonnorEbertExtrema.bonnor_ebert_extrema w φ h1 (cont_at_zero_Ici w φ h1 h3) h3 h4

theorem bonnor_ebert_extrema_h3 :
    necessity% Checked.Math.BonnorEbertExtrema.bonnor_ebert_extrema 3 := by
  refine ⟨fun _ => 0, fun _ => 0, fun s _ => hasDerivWithinAt_const _ _ _,
    continuousWithinAt_const, rfl, ?_⟩
  rintro ⟨ξ, -, -, h0, -, hmax, -⟩
  have h := hmax (ξ 0 + 1) (by simp only [mem_Ici]; linarith) (by intro h; linarith)
  simp at h

theorem bonnor_ebert_extrema_h1 :
    necessity% Checked.Math.BonnorEbertExtrema.bonnor_ebert_extrema 1 := by
  refine ⟨fun _ => 0, fun s => -(s / 3), (continuous_id.div_const 3).neg.continuousWithinAt,
    fun s hs => ?_, rfl, ?_⟩
  · have hs0 : s ≠ 0 := (mem_Ioi.mp hs).ne'
    exact (((hasDerivAt_id' s).div_const 3).neg.hasDerivWithinAt).congr_deriv
      (by rw [Real.exp_zero]; field_simp; ring)
  · rintro ⟨ξ, -, -, h0, -, hmax, -⟩
    have h := hmax (ξ 0 + 1) (by simp only [mem_Ici]; linarith) (by intro h; linarith)
    have hsq0 : 0 < Real.sqrt (4 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    simp only [neg_neg, zero_div, Real.exp_zero, mul_one] at h
    rw [div_lt_div_iff_of_pos_right hsq0] at h
    nlinarith [sq_nonneg (ξ 0), sq_nonneg (ξ 0 + 1)]

theorem bonnor_ebert_extrema_h4 :
    necessity% Checked.Math.BonnorEbertExtrema.bonnor_ebert_extrema 4 := by
  obtain ⟨w, φ, hw, hφ0, hφ, h0⟩ := Checked.Math.BEGlobalExists.exists_global
  obtain ⟨hu, hψ0, hψ⟩ := scaled_hyps_Ici 2 (by norm_num) w φ hw hφ0 hφ
  refine ⟨fun s => w (2 * s) + 2 * Real.log 2, fun s => 2 * φ (2 * s), hu, hψ0, hψ, ?_⟩
  rintro ⟨η, -, -, hη1, -, hglob, -⟩
  obtain ⟨ξ, -, -, hξ1, hξ2, hmax, -⟩ :=
    Checked.Math.BonnorEbertExtrema.bonnor_ebert_extrema w φ hw hφ0 hφ h0
  have hm : ∀ s, (fun s => s ^ 2 * (-(fun s => 2 * φ (2 * s)) s) *
      Real.exp ((fun s => w (2 * s) + 2 * Real.log 2) s / 2) / Real.sqrt (4 * Real.pi)) s =
      Checked.Trust.NecessityM.mass w φ (2 * s) := by
    intro s
    simp only [Checked.Trust.NecessityM.mass]
    rw [show (w (2 * s) + 2 * Real.log 2) / 2 = w (2 * s) / 2 + Real.log 2 by ring, Real.exp_add,
      Real.exp_log (by norm_num)]
    ring
  have h1 := hglob (ξ 0 / 2) (by simp only [mem_Ici]; linarith) (by intro h; linarith)
  have h2 := hmax (2 * η 0) (by simp only [mem_Ici]; linarith) (by intro h; linarith)
  have e1 := hm (ξ 0 / 2)
  have e2 := hm (η 0)
  simp only at e1 e2 h1
  rw [e1, e2, show 2 * (ξ 0 / 2) = ξ 0 by ring] at h1
  simp only [Checked.Trust.NecessityM.mass] at h1
  linarith

end Checked.Trust.NecessityAJ
