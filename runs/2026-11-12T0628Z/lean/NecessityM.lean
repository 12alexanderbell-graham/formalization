import Checked.Trust.NonVacuity
import Checked.Trust.NecessityB
import Checked.Math.BonnorEbert
import Checked.Math.GelfandExists
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds

/-! Hypothesis necessity for the Bonnor–Ebert critical sphere (`Checked.Math.BonnorEbert.bonnor_ebert_critical`,
run 2026-11-12T0628Z). Hypotheses as numbered in `CLAIMS.md`: 1 the length of the interval, 2 the derivative of
w, 3 continuity of φ at the centre, 4 the equation, 5 the centre value w(0) = 0.

* 1, 2, 4 are needed: the zero function (1, 4) and w = 0 with φ(s) = −s/3 (2) meet every other hypothesis, and
  their mass is zero or too large at every radius of the window.
* 3 is redundant: the equation forces continuity of φ at the centre (`Checked.Trust.NCB.cont_at_zero_of_continuous`).
* 5 is needed, by the scaling symmetry of the isothermal equation: if w solves it on [0, 2S] then
  u(s) = w(2s) + 2 log 2 solves it on [0, S], with u(0) = 2 log 2 and mass m_u(s) = m_w(2s). The mass of u
  would then increase strictly up to twice a radius above 6.45, while the mass of w decreases strictly after its
  own critical radius below 7: impossible. -/

namespace Checked.Trust.NecessityM
open Set

/-- The pressure-confined mass of the claim, as a function of the radius. -/
noncomputable def mass (w φ : ℝ → ℝ) (s : ℝ) : ℝ :=
  s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)

theorem bonnor_ebert_critical_r3 : dropped% Checked.Math.BonnorEbert.bonnor_ebert_critical 3 := by
  intro S hS w φ h1 h3 h4
  refine Checked.Math.BonnorEbert.bonnor_ebert_critical S hS w φ h1 ?_ h3 h4
  exact Checked.Trust.NCB.cont_at_zero_of_continuous S (by linarith) 1 w φ (fun y => -Real.exp y)
    (by fun_prop) h1 (fun ξ hξ => (h3 ξ hξ).congr_deriv (by push_cast; ring))

theorem bonnor_ebert_critical_h1 : necessity% Checked.Math.BonnorEbert.bonnor_ebert_critical 1 := by
  refine ⟨0, fun _ => 0, fun _ => 0, fun s _ => hasDerivWithinAt_const _ _ _,
    continuousWithinAt_const, fun s hs => absurd hs (by simp), rfl, ?_⟩
  rintro ⟨ξ₁, -, -, -, -, h5, -⟩
  simp at h5
  norm_num at h5

theorem bonnor_ebert_critical_h4 : necessity% Checked.Math.BonnorEbert.bonnor_ebert_critical 4 := by
  refine ⟨7, le_rfl, fun _ => 0, fun _ => 0, fun s _ => hasDerivWithinAt_const _ _ _,
    continuousWithinAt_const, rfl, ?_⟩
  rintro ⟨ξ₁, -, -, -, -, h5, -⟩
  simp at h5
  norm_num at h5

theorem bonnor_ebert_critical_h2 : necessity% Checked.Math.BonnorEbert.bonnor_ebert_critical 2 := by
  refine ⟨7, le_rfl, fun _ => 0, fun s => -(s / 3), (continuous_id.div_const 3).neg.continuousWithinAt,
    fun s hs => ?_, rfl, ?_⟩
  · have hs0 : s ≠ 0 := (mem_Ioc.mp hs).1.ne'
    exact (((hasDerivAt_id' s).div_const 3).neg.hasDerivWithinAt).congr_deriv
      (by rw [Real.exp_zero]; field_simp; ring)
  · rintro ⟨ξ₁, hlo, -, -, -, -, h6, -⟩
    have hsq : Real.sqrt (4 * Real.pi) ≤ 4 := by
      rw [Real.sqrt_le_left (by norm_num)]
      nlinarith [Real.pi_lt_d2]
    have hsq0 : 0 < Real.sqrt (4 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    simp only [neg_neg, zero_div, Real.exp_zero, mul_one] at h6
    rw [div_le_iff₀ hsq0] at h6
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 1.1822266)]

/-- The scaled solution: w(2s) + 2 log 2 with derivative 2 φ(2s). -/
theorem scaled_hyps (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) 14, HasDerivWithinAt w (φ s) (Icc 0 14) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 14) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) 14,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 14) s) :
    (∀ s ∈ Icc (0 : ℝ) 7, HasDerivWithinAt (fun s => w (2 * s) + 2 * Real.log 2)
        ((fun s => 2 * φ (2 * s)) s) (Icc 0 7) s) ∧
    ContinuousWithinAt (fun s => 2 * φ (2 * s)) (Icc 0 7) 0 ∧
    (∀ s ∈ Ioc (0 : ℝ) 7, HasDerivWithinAt (fun s => 2 * φ (2 * s))
        (-(2 / s * (fun s => 2 * φ (2 * s)) s) - Real.exp ((fun s => w (2 * s) + 2 * Real.log 2) s))
        (Icc 0 7) s) := by
  have hmaps : MapsTo (fun s : ℝ => 2 * s) (Icc 0 7) (Icc 0 14) := by
    intro s hs; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hlin : ∀ s : ℝ, HasDerivWithinAt (fun s : ℝ => 2 * s) 2 (Icc 0 7) s := fun s => by
    simpa using ((hasDerivAt_id s).const_mul (2 : ℝ)).hasDerivWithinAt
  have hlog : Real.exp (2 * Real.log 2) = 4 := by
    rw [show 2 * Real.log 2 = Real.log 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num, Real.exp_log (by norm_num)]
  refine ⟨fun s hs => ?_, ?_, fun s hs => ?_⟩
  · have h := ((hw (2 * s) (hmaps hs)).scomp s (hlin s) hmaps).add_const (2 * Real.log 2)
    refine h.congr_deriv ?_
    simp [smul_eq_mul]
  · have hc : ContinuousWithinAt (fun s : ℝ => 2 * s) (Icc 0 7) 0 :=
      (continuous_const.mul continuous_id).continuousWithinAt
    have h := ContinuousWithinAt.comp (g := φ) (f := fun s : ℝ => 2 * s) (x := 0)
      (by simpa using hφ0) hc hmaps
    exact (continuousWithinAt_const (b := (2 : ℝ))).mul h
  · have hs' : 2 * s ∈ Ioc (0 : ℝ) 14 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h := ((hφ (2 * s) hs').scomp s (hlin s) hmaps).const_mul (2 : ℝ)
    refine h.congr_deriv ?_
    have hs0 : s ≠ 0 := hs.1.ne'
    simp only [smul_eq_mul, Real.exp_add, hlog]
    field_simp
    ring

theorem bonnor_ebert_critical_h5 : necessity% Checked.Math.BonnorEbert.bonnor_ebert_critical 5 := by
  obtain ⟨w, φ, hw, hφ0, hφ, h0⟩ := Checked.Math.GelfandExists.exists_solution 14 (by norm_num)
  obtain ⟨hu, hψ0, hψ⟩ := scaled_hyps w φ hw hφ0 hφ
  refine ⟨7, le_rfl, fun s => w (2 * s) + 2 * Real.log 2, fun s => 2 * φ (2 * s), hu, hψ0, hψ, ?_⟩
  · rintro ⟨η, hη1, hη2, hmono, -, -, -, -, -⟩
    obtain ⟨ξ, hξ1, hξ2, -, hanti, -⟩ :=
      Checked.Math.BonnorEbert.bonnor_ebert_critical 14 (by norm_num) w φ hw hφ0 hφ h0
    -- m_u(s) = m_w(2s)
    have hm : ∀ s, (fun s => s ^ 2 * (-(fun s => 2 * φ (2 * s)) s) *
        Real.exp ((fun s => w (2 * s) + 2 * Real.log 2) s / 2) / Real.sqrt (4 * Real.pi)) s =
        mass w φ (2 * s) := by
      intro s
      simp only [mass]
      rw [show (w (2 * s) + 2 * Real.log 2) / 2 = w (2 * s) / 2 + Real.log 2 by ring, Real.exp_add,
        Real.exp_log (by norm_num)]
      ring
    -- two points of [ξ, 7] ⊆ [0, 2η]: 6.5 < 6.9
    have ha : (6.5 : ℝ) / 2 ∈ Icc 0 η := ⟨by norm_num, by linarith⟩
    have hb : (6.9 : ℝ) / 2 ∈ Icc 0 η := ⟨by norm_num, by linarith⟩
    have hlt := hmono ha hb (by norm_num)
    rw [hm, hm] at hlt
    have hA : (6.5 : ℝ) ∈ Icc ξ 7 := ⟨by linarith, by norm_num⟩
    have hB : (6.9 : ℝ) ∈ Icc ξ 7 := ⟨by linarith, by norm_num⟩
    have hgt := hanti hA hB (by norm_num)
    have e1 : 2 * ((6.5 : ℝ) / 2) = 6.5 := by norm_num
    have e2 : 2 * ((6.9 : ℝ) / 2) = 6.9 := by norm_num
    rw [e1, e2] at hlt
    simp only [mass] at hlt
    linarith

end Checked.Trust.NecessityM
