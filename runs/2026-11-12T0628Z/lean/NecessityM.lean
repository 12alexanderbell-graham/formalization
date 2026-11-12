import Checked.Trust.NonVacuity
import Checked.Trust.NecessityB
import Checked.Math.BonnorEbert
import Checked.Math.GelfandExists
import Checked.Math.Gelfand
import Checked.Math.GProfile
import Checked.Math.ThomasFermi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
  own critical radius below 7: impossible.

The same symmetry with the factor 1/3 shows that hypothesis 5 of `Checked.Math.Gelfand.gelfand_ball_critical`
(the same centre value) is needed; and hypothesis 1 of `Checked.Math.ThomasFermi.tf_initial_slope` (y' = φ) is
needed (an explicit pair with φ' = y^{3/2}/√x but φ(0) = 0). -/

namespace Checked.Trust.NecessityM
open Set Filter Topology

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

/-- Scaling symmetry of the isothermal (Gelfand) equation: if w solves it on [0, cT] (c > 0), then
u(s) = w(cs) + 2 log c, with derivative c φ(cs), solves it on [0, T]. -/
theorem scaled_hyps (c T : ℝ) (hc : 0 < c) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) (c * T), HasDerivWithinAt w (φ s) (Icc 0 (c * T)) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 (c * T)) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) (c * T),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 (c * T)) s) :
    (∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt (fun s => w (c * s) + 2 * Real.log c)
        ((fun s => c * φ (c * s)) s) (Icc 0 T) s) ∧
    ContinuousWithinAt (fun s => c * φ (c * s)) (Icc 0 T) 0 ∧
    (∀ s ∈ Ioc (0 : ℝ) T, HasDerivWithinAt (fun s => c * φ (c * s))
        (-(2 / s * (fun s => c * φ (c * s)) s) - Real.exp ((fun s => w (c * s) + 2 * Real.log c) s))
        (Icc 0 T) s) := by
  have hmaps : MapsTo (fun s : ℝ => c * s) (Icc 0 T) (Icc 0 (c * T)) := by
    intro s hs
    exact ⟨mul_nonneg hc.le hs.1, mul_le_mul_of_nonneg_left hs.2 hc.le⟩
  have hlin : ∀ s : ℝ, HasDerivWithinAt (fun s : ℝ => c * s) c (Icc 0 T) s := fun s => by
    simpa using ((hasDerivAt_id s).const_mul c).hasDerivWithinAt
  have hlog : Real.exp (2 * Real.log c) = c ^ 2 := by
    rw [show (2 : ℝ) * Real.log c = Real.log (c ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
  refine ⟨fun s hs => ?_, ?_, fun s hs => ?_⟩
  · have h := ((hw (c * s) (hmaps hs)).scomp s (hlin s) hmaps).add_const (2 * Real.log c)
    refine h.congr_deriv ?_
    simp [smul_eq_mul]
  · have hcc : ContinuousWithinAt (fun s : ℝ => c * s) (Icc 0 T) 0 :=
      (continuous_const.mul continuous_id).continuousWithinAt
    have h := ContinuousWithinAt.comp (g := φ) (f := fun s : ℝ => c * s) (x := 0)
      (by simpa using hφ0) hcc hmaps
    exact (continuousWithinAt_const (b := c)).mul h
  · have hs' : c * s ∈ Ioc (0 : ℝ) (c * T) :=
      ⟨mul_pos hc hs.1, mul_le_mul_of_nonneg_left hs.2 hc.le⟩
    have h := ((hφ (c * s) hs').scomp s (hlin s) hmaps).const_mul c
    refine h.congr_deriv ?_
    have hs0 : s ≠ 0 := hs.1.ne'
    have hc0 : c ≠ 0 := hc.ne'
    simp only [smul_eq_mul, Real.exp_add, hlog]
    field_simp

theorem bonnor_ebert_critical_h5 : necessity% Checked.Math.BonnorEbert.bonnor_ebert_critical 5 := by
  obtain ⟨w, φ, hw, hφ0, hφ, h0⟩ := Checked.Math.GelfandExists.exists_solution (2 * 7) (by norm_num)
  obtain ⟨hu, hψ0, hψ⟩ := scaled_hyps 2 7 (by norm_num) w φ hw hφ0 hφ
  refine ⟨7, le_rfl, fun s => w (2 * s) + 2 * Real.log 2, fun s => 2 * φ (2 * s), hu, hψ0, hψ, ?_⟩
  · rintro ⟨η, hη1, hη2, hmono, -, -, -, -, -⟩
    obtain ⟨ξ, hξ1, hξ2, -, hanti, -⟩ :=
      Checked.Math.BonnorEbert.bonnor_ebert_critical (2 * 7) (by norm_num) w φ hw hφ0 hφ h0
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

/-! ### Gelfand ball: the centre value w(0) = 0 is needed (scaling by 1/3) -/

/-- Hypothesis 5 of `gelfand_ball_critical` (w(0) = 0) is needed: u(s) = w(s/3) − 2 log 3 solves the equation on
[0, 41/10] when w solves it on [0, 41/30]; then s² e^{u(s)} = (s/3)² e^{w(s/3)} ≤ (s/3)² (w ≤ 0 by
`Checked.Math.GProfile.profile_bounds`), below the claimed maximum value at every point of [0, 41/10]. -/
theorem gelfand_ball_critical_h5 : necessity% Checked.Math.Gelfand.gelfand_ball_critical 5 := by
  obtain ⟨w, φ, hw, hφ0, hφ, h0⟩ :=
    Checked.Math.GelfandExists.exists_solution ((1 / 3) * (41 / 10)) (by norm_num)
  obtain ⟨hu, hψ0, hψ⟩ := scaled_hyps (1 / 3) (41 / 10) (by norm_num) w φ hw hφ0 hφ
  obtain ⟨-, hwb, -⟩ := Checked.Math.GProfile.profile_bounds ((1 / 3) * (41 / 10)) (by norm_num)
    w φ hw hφ0 hφ h0
  refine ⟨41 / 10, le_rfl, fun s => w ((1 / 3) * s) + 2 * Real.log (1 / 3),
    fun s => (1 / 3) * φ ((1 / 3) * s), hu, hψ0, hψ, ?_⟩
  rintro ⟨s₁, hlo, hhi, -, hv, -⟩
  have hmem : (1 / 3) * s₁ ∈ Icc (0 : ℝ) ((1 / 3) * (41 / 10)) := ⟨by linarith, by linarith⟩
  have hw0 : w ((1 / 3) * s₁) ≤ 0 := (hwb _ hmem).2
  have hlog : Real.exp (2 * Real.log (1 / 3)) = (1 / 3) ^ 2 := by
    rw [show (2 : ℝ) * Real.log (1 / 3) = Real.log ((1 / 3) ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
  rw [Real.exp_add, hlog] at hv
  have he : Real.exp (w ((1 / 3) * s₁)) ≤ 1 := Real.exp_le_one_iff.mpr hw0
  have hs2 : 0 ≤ s₁ ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left he hs2]

/-! ### Thomas–Fermi: the relation y' = φ is needed -/

/-- Hypothesis 1 of `tf_initial_slope` (φ is the derivative of y) is needed: y = 1/(1 + √x)² and
φ = 1 − 1/(1 + √x)² meet every other hypothesis (φ' = y^{3/2}/√x, y(0) = 1, y > 0, y → 0) and φ(0) = 0. -/
theorem tf_initial_slope_h1 : necessity% Checked.Math.ThomasFermi.tf_initial_slope 1 := by
  refine ⟨fun x => 1 / (1 + Real.sqrt x) ^ 2, fun x => 1 - 1 / (1 + Real.sqrt x) ^ 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hs : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x := by
      simpa using Real.hasDerivAt_sqrt hx.ne'
    have hb : 0 < 1 + Real.sqrt x := by positivity
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
    have h1 := ((hs.const_add 1).pow 2).inv (by simp only [Pi.pow_apply]; positivity)
    have h2 := (h1.const_mul (-1 : ℝ)).const_add 1
    have key : (1 / (1 + Real.sqrt x) ^ 2) ^ ((3 : ℝ) / 2) = 1 / (1 + Real.sqrt x) ^ 3 := by
      rw [show (1 : ℝ) / (1 + Real.sqrt x) ^ 2 = (1 / (1 + Real.sqrt x)) ^ (2 : ℝ) by
        rw [Real.rpow_two]; field_simp, ← Real.rpow_mul (by positivity)]
      rw [show (2 : ℝ) * (3 / 2) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      field_simp
    rw [key]
    refine (h2.congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp only [Pi.pow_apply]
      field_simp
      ring
    · exact Filter.Eventually.of_forall fun z => by simp [one_div, neg_mul, sub_eq_add_neg]
  · have hc : Continuous fun x : ℝ => 1 - 1 / (1 + Real.sqrt x) ^ 2 := by
      refine continuous_const.sub (continuous_const.div (by fun_prop) fun x => by positivity)
    exact hc.continuousWithinAt
  · simp
  · intro x _; positivity
  · have h1 : Tendsto (fun x : ℝ => 1 + Real.sqrt x) atTop atTop :=
      tendsto_atTop_add_const_left _ _ Real.tendsto_sqrt_atTop
    have h2 := (tendsto_pow_atTop (two_ne_zero)).comp h1
    simpa [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp h2
  · simp only [sub_self, Real.sqrt_zero, add_zero, one_pow, div_one]
    norm_num

end Checked.Trust.NecessityM
