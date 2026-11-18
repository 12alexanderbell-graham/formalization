import Checked.Trust.NecessityAQ
import Checked.Cosmography.B1FitRL19
import Checked.Cosmography.B1L19Curved

/-!
# Hypothesis necessity, B1 family: fit residuals, source redshifts, the law, and the curved pair (trust track T2b)

Run 2026-11-18T0628Z. Ten hypotheses of three B1 headlines decided NEEDED with exact or certified models and
no new certificate files.

* **`fit_direction`** (every cubic log-polynomial that matches the exact distance modulus at three
  redshifts within a twentieth of a magnitude lies beyond a line through the Lusso et al. 2019 ΛCDM point): each of the three
  residual conditions, each of the three source redshifts and the expansion law are NEEDED. Witness model:
  Einstein–de Sitter (`ea`, the scale factor `s` to the power two thirds observed at one), which obeys the
  flat law at density one; its distance is three times `Z (1 − √(1/Z))` at `1 + z = Z`
  (`ea_dL`, from the bridge of `NecessityAQ`). With one residual condition dropped, a cubic matching the
  other two distance moduli exactly enough is found on the wrong side of the line; with one source
  redshift dropped, that source is placed at another source and the same cubics serve; without the law,
  the model's distances with the law's density read as zero give a cubic matching all three on the wrong side.
* **`rl19_box_unmatched`** (no cubic in the Risaliti–Lusso 2019 coefficient box matches flat ΛCDM with
  density in the unit interval): the redshift of the middle source is NEEDED; with that source placed at
  the nearest one, a box cubic matches the Einstein–de Sitter distance moduli at the two remaining
  redshifts.
* **`l19_sq_curved`, `l19_sqg_curved`** (curved Lusso et al. 2019 central fits): the upper density bound
  is NEEDED, with the flat model of `NecessityAQ` (zero curvature constant, total density one) at density one
  hundred: a twenty-step lower sum and a four-step upper sum of its increasing integrand (`J53_100`) bound
  the growth of each residual below the stated margins.

Every residual is checked through two-sided interval bounds (`resid_band`): the distance and the polynomial
distance each lie in an interval and the intervals agree to two percent. Numbers chosen by
`runs/2026-11-18T0628Z/scripts/eds_bounds.py` and `emit_j100.py` (exact rationals); Lean checks every one.
-/

namespace Checked.Trust.NCAR

open Set Filter Topology MeasureTheory Real
open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1
open Checked.Trust.NCAQ Checked.Cosmography.B1L19 Checked.Cosmography.BambaK
open Checked.Cosmography.Transverse

/-- The Einstein–de Sitter scale factor `s^{2/3}`, observed at `t₀ = 1`. -/
noncomputable def ea (s : ℝ) : ℝ := s ^ (2 / 3 : ℝ)

theorem ea_hasDerivAt (s : ℝ) (h0 : 0 < s) :
    HasDerivAt ea ((2 / 3) * s ^ ((2 / 3 : ℝ) - 1)) s :=
  Real.hasDerivAt_rpow_const (Or.inl h0.ne')

theorem ea_pos (s : ℝ) (h0 : 0 < s) : 0 < ea s := Real.rpow_pos_of_pos h0 _

theorem ea_one : ea 1 = 1 := by simp [ea]

theorem ea_hubble (s : ℝ) (h0 : 0 < s) : hubble ea s = 2 / 3 * (1 / s) := by
  unfold hubble
  rw [(ea_hasDerivAt s h0).deriv]
  simp only [ea]
  rw [Real.rpow_sub h0, Real.rpow_one]
  have : 0 < s ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos h0 _
  field_simp

theorem ea_H0 : hubble ea 1 = 2 / 3 := by rw [ea_hubble 1 one_pos]; norm_num

theorem ea_z3 (s : ℝ) (h0 : 0 < s) : (1 + redshift ea 1 s) ^ 3 = 1 / s ^ 2 := by
  unfold redshift
  rw [ea_one, show 1 + (1 / ea s - 1) = 1 / ea s by ring, div_pow, one_pow]
  simp only [ea]
  rw [cube23 _ h0]

/-- The Einstein–de Sitter law (density one) holds on `(0, 1]`. -/
theorem ea_law (s : ℝ) (h0 : 0 < s) :
    hubble ea s = hubble ea 1 * √(1 * (1 + redshift ea 1 s) ^ 3 + 1 - 1) := by
  rw [ea_z3 s h0, ea_hubble s h0, ea_H0]
  rw [show 1 * (1 / s ^ 2) + 1 - 1 = (1 / s) ^ 2 by ring, Real.sqrt_sq (by positivity)]

/-- Source time with `1 + z = Z`. -/
noncomputable def tE (Z : ℝ) : ℝ := (Z ^ (3 / 2 : ℝ))⁻¹

theorem tE_props (Z : ℝ) (hZ : 1 ≤ Z) :
    0 < tE Z ∧ tE Z ≤ 1 ∧ redshift ea 1 (tE Z) = Z - 1 ∧ ea (tE Z) = Z⁻¹ := by
  have hZ0 : 0 < Z := by linarith
  have hZp : 1 ≤ Z ^ (3 / 2 : ℝ) := Real.one_le_rpow hZ (by norm_num)
  have hea : ea (tE Z) = Z⁻¹ := by
    simp only [ea, tE]
    rw [Real.inv_rpow (by positivity), ← Real.rpow_mul hZ0.le]
    norm_num
  refine ⟨by unfold tE; positivity, inv_le_one_of_one_le₀ hZp, ?_, hea⟩
  unfold redshift; rw [ea_one, hea]; field_simp

theorem tE_anti (Z₁ Z₂ : ℝ) (hZ : 1 ≤ Z₁) (h12 : Z₁ ≤ Z₂) : tE Z₂ ≤ tE Z₁ := by
  unfold tE
  apply inv_anti₀ (Real.rpow_pos_of_pos (by linarith) _)
  exact Real.rpow_le_rpow (by linarith) h12 (by norm_num)

theorem ea_hyps (t : ℝ) (ht0 : 0 < t) :
    (∀ s ∈ Set.Icc t 1, 0 < ea s) ∧ (∀ s ∈ Set.Icc t 1, DifferentiableAt ℝ ea s) ∧
      0 < hubble ea 1 ∧
      (∀ s ∈ Set.Icc t 1, hubble ea s = hubble ea 1 * √(1 * (1 + redshift ea 1 s) ^ 3 + 1 - 1)) :=
  ⟨fun s hs => ea_pos s (by linarith [hs.1]),
   fun s hs => (ea_hasDerivAt s (by linarith [hs.1])).differentiableAt,
   by rw [ea_H0]; norm_num,
   fun s hs => ea_law s (by linarith [hs.1])⟩

/-- The distance in the model: `d_L = 3 Z (1 − √(1/Z))`. -/
theorem ea_dL (Z : ℝ) (hZ : 1 ≤ Z) :
    lumDistFlat ea 1 (tE Z) = 3 * Z * (1 - √(1 / Z)) := by
  obtain ⟨ht0, ht1, hz, hea⟩ := tE_props Z hZ
  obtain ⟨hp, hd, hH₀, hH⟩ := ea_hyps (tE Z) ht0
  have hbr := bridge 1 (by norm_num) ea _ _ ht1 hp hd hH₀ hH
  rw [hbr, hz, hea, ea_one, ea_H0]
  have hv : √(Z⁻¹ / 1) ≤ 1 := by
    rw [div_one, Real.sqrt_le_one]; exact inv_le_one_of_one_le₀ hZ
  simp only [sub_self, zero_mul, add_zero, Real.sqrt_one, div_one, intervalIntegral.integral_const,
    smul_eq_mul, one_div]
  ring


theorem ea_src (Z : ℝ) (hZ : 1 ≤ Z) :
    redshift ea 1 (tE Z) = Z - 1 ∧ lumDistFlat ea 1 (tE Z) = 3 * Z * (1 - √(1 / Z)) :=
  ⟨(tE_props Z hZ).2.2.1, ea_dL Z hZ⟩

/-- The bracket of the cubic log-polynomial. -/
noncomputable def Bc (a₂ a₃ x : ℝ) : ℝ := x + a₂ * x ^ 2 + a₃ * x ^ 3

theorem poly3_eq (a₂ a₃ H k z : ℝ) (hz : Real.log (1 + z) = k * Real.log 2) :
    logPolyDL3 a₂ a₃ H z = Real.log 10 / H * Bc a₂ a₃ (k * (Real.log 2 / Real.log 10)) := by
  unfold logPolyDL3 Bc Real.logb; rw [hz]; ring

theorem log_s2 : Real.log (1 + (√2 - 1)) = 1 / 2 * Real.log 2 := by
  rw [show 1 + (√2 - 1) = √2 by ring, Real.log_sqrt (by norm_num)]; ring

theorem resid_small (y : ℝ) (h1 : 0.98 ≤ y) (h2 : y ≤ 1.02) : |5 * Real.logb 10 y - 0| ≤ 1 / 20 := by
  have hy : 0 < y := by linarith
  have hu := Real.log_le_sub_one_of_pos hy
  have hd := Real.one_sub_inv_le_log_of_pos hy
  have hinv : y⁻¹ ≤ 1 / 0.98 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) h1
  obtain ⟨l1, l2⟩ := log10_bd
  have hL : 0 < Real.log 10 := by linarith
  rw [sub_zero, abs_le, Real.logb,
    show 5 * (Real.log y / Real.log 10) = (5 * Real.log y) / Real.log 10 by ring]
  constructor
  · rw [le_div_iff₀ hL]; norm_num at hinv ⊢; nlinarith
  · rw [div_le_iff₀ hL]; nlinarith

/-- Interval form: if the distance and the polynomial distance lie in intervals whose ends agree to
two percent, the residual distance modulus is within 1/20 mag of zero. -/
theorem resid_band (L B d H Ll Lu Bl Bu dl du : ℝ) (hH : 0 < H) (hL : Ll ≤ L) (hL' : L ≤ Lu)
    (hB : Bl ≤ B) (hB' : B ≤ Bu) (hd : dl ≤ d) (hd' : d ≤ du) (hLl : 0 < Ll) (hBl : 0 < Bl)
    (c1 : 0.98 * (Lu / H * Bu) ≤ dl) (c2 : du ≤ 1.02 * (Ll / H * Bl)) :
    |5 * Real.logb 10 (d / (L / H * B)) - 0| ≤ 1 / 20 := by
  have hPl : Ll / H * Bl ≤ L / H * B :=
    mul_le_mul (div_le_div_of_nonneg_right hL hH.le) hB hBl.le (div_nonneg (by linarith) hH.le)
  have hPu : L / H * B ≤ Lu / H * Bu :=
    mul_le_mul (div_le_div_of_nonneg_right hL' hH.le) hB' (by linarith) (div_nonneg (by linarith) hH.le)
  have hP0 : 0 < Ll / H * Bl := by positivity
  have hP : 0 < L / H * B := by linarith
  apply resid_small
  · rw [le_div_iff₀ hP]; linarith
  · rw [div_le_iff₀ hP]; linarith

theorem pos_of (L B H Ll Bl : ℝ) (hH : 0 < H) (hL : Ll ≤ L) (hB : Bl ≤ B) (hLl : 0 < Ll)
    (hBl : 0 < Bl) : 0 < L / H * B :=
  mul_pos (div_pos (by linarith) hH) (by linarith)

theorem v1_bd : (0.8408 : ℝ) ≤ √(1 / √2) ∧ √(1 / √2) ≤ (0.8409 : ℝ) := by
  obtain ⟨a, b⟩ := sqrt2_bd
  have hp : 0 < √2 := by positivity
  constructor
  · rw [show (0.8408 : ℝ) = √(0.8408 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_le_sqrt; rw [le_div_iff₀ hp]; nlinarith
  · rw [show (0.8409 : ℝ) = √(0.8409 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_le_sqrt; rw [div_le_iff₀ hp]; nlinarith

theorem d1_bd : (0.675002 : ℝ) ≤ 3 * √2 * (1 - √(1 / √2)) ∧ 3 * √2 * (1 - √(1 / √2)) ≤ (0.675432 : ℝ) := by
  obtain ⟨a, b⟩ := sqrt2_bd
  obtain ⟨c, d⟩ := v1_bd
  have h1 : 1.41421 * (1 - 0.8409) ≤ √2 * (1 - √(1 / √2)) :=
    mul_le_mul a (by linarith) (by norm_num) (by linarith)
  have h2 : √2 * (1 - √(1 / √2)) ≤ 1.41422 * (1 - 0.8408) :=
    mul_le_mul b (by linarith) (by linarith) (by norm_num)
  constructor <;> nlinarith

theorem d3_bd : (3.439075 : ℝ) ≤ 3 * (2 * √2) * (1 - √(1 / (2 * √2))) ∧
    3 * (2 * √2) * (1 - √(1 / (2 * √2))) ≤ (3.439949 : ℝ) := by
  obtain ⟨a, b⟩ := sqrt2_bd
  obtain ⟨c, d⟩ := v3_bd
  have h1 : 1.41421 * (1 - 0.5947) ≤ √2 * (1 - √(1 / (2 * √2))) :=
    mul_le_mul a (by linarith) (by norm_num) (by linarith)
  have h2 : √2 * (1 - √(1 / (2 * √2))) ≤ 1.41422 * (1 - 0.5946) :=
    mul_le_mul b (by linarith) (by linarith) (by norm_num)
  constructor <;> nlinarith

theorem d5_bd : (9.834416 : ℝ) ≤ 3 * (4 * √2) * (1 - √(1 / (4 * √2))) ∧
    3 * (4 * √2) * (1 - √(1 / (4 * √2))) ≤ (9.836183 : ℝ) := by
  obtain ⟨a, b⟩ := sqrt2_bd
  obtain ⟨c, d⟩ := v5_bd
  have h1 : 1.41421 * (1 - 0.4205) ≤ √2 * (1 - √(1 / (4 * √2))) :=
    mul_le_mul a (by linarith) (by norm_num) (by linarith)
  have h2 : √2 * (1 - √(1 / (4 * √2))) ≤ 1.41422 * (1 - 0.4204) :=
    mul_le_mul b (by linarith) (by linarith) (by norm_num)
  constructor <;> nlinarith

theorem log2L_bd : (1.595951 : ℝ) ≤ Real.log 2 * Real.log 10 ∧ Real.log 2 * Real.log 10 ≤ (1.5961 : ℝ) := by
  obtain ⟨l1, l2⟩ := log10_bd
  have a := Real.log_two_gt_d9
  have b := Real.log_two_lt_d9
  constructor <;> nlinarith

/-- The conclusion of `fit_direction` fails as soon as its linear form in `λ = log₁₀ 2` does. -/
theorem concl_neg (a₂ a₃ Ω : ℝ)
    (h : 20 / 3 * ((Real.log 2 / Real.log 10) * a₃ - Real.log 2 * Real.log 10 * (9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6))
      ≤ a₂ - Real.log 10 * (3 / 2 - 3 / 4 * Ω) + 1 / 2) :
    ¬ (a₂ - lusA2 Ω + 1 / 2 < 20 / 3 * Real.logb 10 2 * (a₃ - lusA3 Ω)) := by
  have hL : Real.log 10 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [not_lt]
  unfold lusA2 lusA3 Real.logb
  convert h using 1
  field_simp

theorem B_fit17_1 : (0.432004 : ℝ) ≤ Bc (47 / 4 : ℝ) (9 / 2 : ℝ) (1 / 2 * (Real.log 2 / Real.log 10)) ∧
    Bc (47 / 4 : ℝ) (9 / 2 : ℝ) (1 / 2 * (Real.log 2 / Real.log 10)) ≤ (0.432102 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

theorem B_fit17_3 : (3.261156 : ℝ) ≤ Bc (47 / 4 : ℝ) (9 / 2 : ℝ) (3 / 2 * (Real.log 2 / Real.log 10)) ∧
    Bc (47 / 4 : ℝ) (9 / 2 : ℝ) (3 / 2 * (Real.log 2 / Real.log 10)) ≤ (3.262019 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

theorem B_fit17_5 : (9.324154 : ℝ) ≤ Bc (47 / 4 : ℝ) (9 / 2 : ℝ) (5 / 2 * (Real.log 2 / Real.log 10)) ∧
    Bc (47 / 4 : ℝ) (9 / 2 : ℝ) (5 / 2 * (Real.log 2 / Real.log 10)) ≤ (9.326788 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

theorem B_fit18_1 : (1.040424 : ℝ) ≤ Bc (171 / 4 : ℝ) ((-23):ℝ) (1 / 2 * (Real.log 2 / Real.log 10)) ∧
    Bc (171 / 4 : ℝ) ((-23):ℝ) (1 / 2 * (Real.log 2 / Real.log 10)) ≤ (1.040734 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

theorem B_fit18_3 : (7.048818 : ℝ) ≤ Bc (171 / 4 : ℝ) ((-23):ℝ) (3 / 2 * (Real.log 2 / Real.log 10)) ∧
    Bc (171 / 4 : ℝ) ((-23):ℝ) (3 / 2 * (Real.log 2 / Real.log 10)) ≤ (7.05204 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

theorem B_fit18_5 : (15.156223 : ℝ) ≤ Bc (171 / 4 : ℝ) ((-23):ℝ) (5 / 2 * (Real.log 2 / Real.log 10)) ∧
    Bc (171 / 4 : ℝ) ((-23):ℝ) (5 / 2 * (Real.log 2 / Real.log 10)) ≤ (15.166666 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

theorem B_fit19_1 : (0.313813 : ℝ) ≤ Bc (8:ℝ) (-21 / 4 : ℝ) (1 / 2 * (Real.log 2 / Real.log 10)) ∧
    Bc (8:ℝ) (-21 / 4 : ℝ) (1 / 2 * (Real.log 2 / Real.log 10)) ≤ (0.313889 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

theorem B_fit19_3 : (1.598994 : ℝ) ≤ Bc (8:ℝ) (-21 / 4 : ℝ) (3 / 2 * (Real.log 2 / Real.log 10)) ∧
    Bc (8:ℝ) (-21 / 4 : ℝ) (3 / 2 * (Real.log 2 / Real.log 10)) ≤ (1.599681 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

theorem B_fit19_5 : (3.044694 : ℝ) ≤ Bc (8:ℝ) (-21 / 4 : ℝ) (5 / 2 * (Real.log 2 / Real.log 10)) ∧
    Bc (8:ℝ) (-21 / 4 : ℝ) (5 / 2 * (Real.log 2 / Real.log 10)) ≤ (3.046892 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

theorem B_fit9_1 : (0.173763 : ℝ) ≤ Bc (1 / 2 : ℝ) (7 / 2 : ℝ) (1 / 2 * (Real.log 2 / Real.log 10)) ∧
    Bc (1 / 2 : ℝ) (7 / 2 : ℝ) (1 / 2 * (Real.log 2 / Real.log 10)) ≤ (0.173791 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

theorem B_fit9_3 : (0.875617 : ℝ) ≤ Bc (1 / 2 : ℝ) (7 / 2 : ℝ) (3 / 2 * (Real.log 2 / Real.log 10)) ∧
    Bc (1 / 2 : ℝ) (7 / 2 : ℝ) (3 / 2 * (Real.log 2 / Real.log 10)) ≤ (0.875834 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

theorem B_fit9_5 : (2.527197 : ℝ) ≤ Bc (1 / 2 : ℝ) (7 / 2 : ℝ) (5 / 2 * (Real.log 2 / Real.log 10)) ∧
    Bc (1 / 2 : ℝ) (7 / 2 : ℝ) (5 / 2 * (Real.log 2 / Real.log 10)) ≤ (2.527968 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

theorem B_rl11_1 : (0.234312 : ℝ) ≤ Bc (69 / 20 : ℝ) (83 / 50 : ℝ) (1 / 2 * (Real.log 2 / Real.log 10)) ∧
    Bc (69 / 20 : ℝ) (83 / 50 : ℝ) (1 / 2 * (Real.log 2 / Real.log 10)) ≤ (0.234356 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

theorem B_rl11_3 : (1.307652 : ℝ) ≤ Bc (69 / 20 : ℝ) (83 / 50 : ℝ) (3 / 2 * (Real.log 2 / Real.log 10)) ∧
    Bc (69 / 20 : ℝ) (83 / 50 : ℝ) (3 / 2 * (Real.log 2 / Real.log 10)) ≤ (1.307961 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

theorem B_rl11_5 : (3.413648 : ℝ) ≤ Bc (69 / 20 : ℝ) (83 / 50 : ℝ) (5 / 2 * (Real.log 2 / Real.log 10)) ∧
    Bc (69 / 20 : ℝ) (83 / 50 : ℝ) (5 / 2 * (Real.log 2 / Real.log 10)) ≤ (3.41455 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)


theorem ea_ord : tE (4 * √2) ≤ tE (2 * √2) ∧ tE (2 * √2) ≤ tE √2 ∧ tE √2 ≤ 1 ∧ 0 < tE (4 * √2) ∧
    0 < tE (2 * √2) := by
  obtain ⟨s1, -⟩ := sqrt2_bd
  exact ⟨tE_anti _ _ (by linarith) (by linarith), tE_anti _ _ (by linarith) (by linarith),
    (tE_props √2 (by linarith)).2.1, (tE_props _ (by linarith)).1, (tE_props _ (by linarith)).1⟩

theorem ea_S1 : redshift ea 1 (tE √2) = √2 - 1 ∧ lumDistFlat ea 1 (tE √2) = 3 * √2 * (1 - √(1 / √2)) :=
  ea_src √2 (by obtain ⟨s1, -⟩ := sqrt2_bd; linarith)
theorem ea_S3 : redshift ea 1 (tE (2 * √2)) = 2 * √2 - 1 ∧
    lumDistFlat ea 1 (tE (2 * √2)) = 3 * (2 * √2) * (1 - √(1 / (2 * √2))) :=
  ea_src _ (by obtain ⟨s1, -⟩ := sqrt2_bd; linarith)
theorem ea_S5 : redshift ea 1 (tE (4 * √2)) = 4 * √2 - 1 ∧
    lumDistFlat ea 1 (tE (4 * √2)) = 3 * (4 * √2) * (1 - √(1 / (4 * √2))) :=
  ea_src _ (by obtain ⟨s1, -⟩ := sqrt2_bd; linarith)

/-- Without the residual condition at `1 + z = √2`: in the Einstein–de Sitter model the cubic
`a₂ = 47/4`, `a₃ = 9/2` matches the distance modulus at `2√2` and `4√2` within 1/20 mag and lies on
the wrong side of the line. -/
theorem fit_direction_h17 : necessity% Checked.Cosmography.B1Fit.fit_direction 17 := by
  obtain ⟨o53, o31, o10, p5, -⟩ := ea_ord
  obtain ⟨hp, hd, hH₀, hH⟩ := ea_hyps _ p5
  obtain ⟨l1, l2⟩ := log10_bd
  obtain ⟨m1, m2⟩ := lam_bd
  obtain ⟨n1, n2⟩ := log2L_bd
  refine ⟨1, by norm_num, le_rfl, ea, _, _, _, 1, o53, o31, o10, hp, hd, hH₀, hH, ea_S1.1, ea_S3.1, ea_S5.1,
    (47 / 4 : ℝ), (9 / 2 : ℝ), 2.1832, 0, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit17_1.1 (by norm_num) (by norm_num)
  · rw [ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit17_3.1 (by norm_num) (by norm_num)
  · rw [ea_S5.1, poly3_eq _ _ _ (5 / 2) _ log_4s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit17_5.1 (by norm_num) (by norm_num)
  · rw [ea_S3.2, ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit17_3.1 B_fit17_3.2 d3_bd.1 d3_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [ea_S5.2, ea_S5.1, poly3_eq _ _ _ (5 / 2) _ log_4s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit17_5.1 B_fit17_5.2 d5_bd.1 d5_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · apply concl_neg; norm_num; nlinarith

/-- Without the residual condition at `1 + z = 2√2`: the cubic `a₂ = 171/4`, `a₃ = −23` matches at `√2` and `4√2`. -/
theorem fit_direction_h18 : necessity% Checked.Cosmography.B1Fit.fit_direction 18 := by
  obtain ⟨o53, o31, o10, p5, p3⟩ := ea_ord
  obtain ⟨l1, l2⟩ := log10_bd
  obtain ⟨m1, m2⟩ := lam_bd
  obtain ⟨n1, n2⟩ := log2L_bd
  obtain ⟨hp, hd, hH₀, hH⟩ := ea_hyps _ p5
  refine ⟨1, by norm_num, le_rfl, ea, _, _, _, 1, o53, o31, o10, hp, hd, hH₀, hH, ea_S1.1, ea_S3.1, ea_S5.1,
    (171 / 4 : ℝ), (-23:ℝ), 3.5495, 0, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit18_1.1 (by norm_num) (by norm_num)
  · rw [ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit18_3.1 (by norm_num) (by norm_num)
  · rw [ea_S5.1, poly3_eq _ _ _ (5 / 2) _ log_4s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit18_5.1 (by norm_num) (by norm_num)
  · rw [ea_S1.2, ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit18_1.1 B_fit18_1.2 d1_bd.1 d1_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [ea_S5.2, ea_S5.1, poly3_eq _ _ _ (5 / 2) _ log_4s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit18_5.1 B_fit18_5.2 d5_bd.1 d5_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · apply concl_neg; norm_num; nlinarith

/-- Without the residual condition at `1 + z = 4√2`: the cubic `a₂ = 8`, `a₃ = −21/4` matches at `√2` and `2√2`. -/
theorem fit_direction_h19 : necessity% Checked.Cosmography.B1Fit.fit_direction 19 := by
  obtain ⟨o53, o31, o10, p5, p3⟩ := ea_ord
  obtain ⟨l1, l2⟩ := log10_bd
  obtain ⟨m1, m2⟩ := lam_bd
  obtain ⟨n1, n2⟩ := log2L_bd
  obtain ⟨hp, hd, hH₀, hH⟩ := ea_hyps _ p5
  refine ⟨1, by norm_num, le_rfl, ea, _, _, _, 1, o53, o31, o10, hp, hd, hH₀, hH, ea_S1.1, ea_S3.1, ea_S5.1,
    (8:ℝ), (-21 / 4 : ℝ), 1.0706, 0, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit19_1.1 (by norm_num) (by norm_num)
  · rw [ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit19_3.1 (by norm_num) (by norm_num)
  · rw [ea_S5.1, poly3_eq _ _ _ (5 / 2) _ log_4s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit19_5.1 (by norm_num) (by norm_num)
  · rw [ea_S1.2, ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit19_1.1 B_fit19_1.2 d1_bd.1 d1_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [ea_S3.2, ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit19_3.1 B_fit19_3.2 d3_bd.1 d3_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · apply concl_neg; norm_num; nlinarith

/-- Without the expansion law: the Einstein–de Sitter scale factor with the law's density read as zero; the cubic `a₂ = 1/2`, `a₃ = 7/2` matches all three distance moduli and lies on the wrong side of the line through the density-zero point. -/
theorem fit_direction_h9 : necessity% Checked.Cosmography.B1Fit.fit_direction 9 := by
  obtain ⟨o53, o31, o10, p5, p3⟩ := ea_ord
  obtain ⟨l1, l2⟩ := log10_bd
  obtain ⟨m1, m2⟩ := lam_bd
  obtain ⟨n1, n2⟩ := log2L_bd
  obtain ⟨hp, hd, hH₀, -⟩ := ea_hyps _ p5
  refine ⟨0, by norm_num, by norm_num, ea, _, _, _, 1, o53, o31, o10, hp, hd, hH₀, ea_S1.1, ea_S3.1, ea_S5.1,
    (1 / 2 : ℝ), (7 / 2 : ℝ), 0.5895, 0, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit9_1.1 (by norm_num) (by norm_num)
  · rw [ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit9_3.1 (by norm_num) (by norm_num)
  · rw [ea_S5.1, poly3_eq _ _ _ (5 / 2) _ log_4s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit9_5.1 (by norm_num) (by norm_num)
  · rw [ea_S1.2, ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit9_1.1 B_fit9_1.2 d1_bd.1 d1_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [ea_S3.2, ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit9_3.1 B_fit9_3.2 d3_bd.1 d3_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [ea_S5.2, ea_S5.1, poly3_eq _ _ _ (5 / 2) _ log_4s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit9_5.1 B_fit9_5.2 d5_bd.1 d5_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · apply concl_neg; norm_num; nlinarith

/-- Without the redshift of the nearest source: that source placed at the middle one (`1 + z = 2√2`); the cubic of `fit_direction_h17` matches both distinct sources. -/
theorem fit_direction_h10 : necessity% Checked.Cosmography.B1Fit.fit_direction 10 := by
  obtain ⟨o53, o31, o10, p5, p3⟩ := ea_ord
  obtain ⟨l1, l2⟩ := log10_bd
  obtain ⟨m1, m2⟩ := lam_bd
  obtain ⟨n1, n2⟩ := log2L_bd
  obtain ⟨hp, hd, hH₀, hH⟩ := ea_hyps _ p5
  refine ⟨1, by norm_num, le_rfl, ea, _, tE (2 * √2), tE (2 * √2), 1, o53, le_rfl, le_trans o31 o10, hp, hd, hH₀, hH, ea_S3.1, ea_S5.1,
    (47 / 4 : ℝ), (9 / 2 : ℝ), 2.1832, 0, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit17_3.1 (by norm_num) (by norm_num)
  · rw [ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit17_3.1 (by norm_num) (by norm_num)
  · rw [ea_S5.1, poly3_eq _ _ _ (5 / 2) _ log_4s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit17_5.1 (by norm_num) (by norm_num)
  · rw [ea_S3.2, ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit17_3.1 B_fit17_3.2 d3_bd.1 d3_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [ea_S3.2, ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit17_3.1 B_fit17_3.2 d3_bd.1 d3_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [ea_S5.2, ea_S5.1, poly3_eq _ _ _ (5 / 2) _ log_4s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit17_5.1 B_fit17_5.2 d5_bd.1 d5_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · apply concl_neg; norm_num; nlinarith

/-- Without the redshift of the middle source: that source placed at the nearest one (`1 + z = √2`); the cubic of `fit_direction_h18` matches both distinct sources. -/
theorem fit_direction_h11 : necessity% Checked.Cosmography.B1Fit.fit_direction 11 := by
  obtain ⟨o53, o31, o10, p5, p3⟩ := ea_ord
  obtain ⟨l1, l2⟩ := log10_bd
  obtain ⟨m1, m2⟩ := lam_bd
  obtain ⟨n1, n2⟩ := log2L_bd
  obtain ⟨hp, hd, hH₀, hH⟩ := ea_hyps _ p5
  refine ⟨1, by norm_num, le_rfl, ea, _, tE √2, tE √2, 1, le_trans o53 o31, le_rfl, o10, hp, hd, hH₀, hH, ea_S1.1, ea_S5.1,
    (171 / 4 : ℝ), (-23:ℝ), 3.5495, 0, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit18_1.1 (by norm_num) (by norm_num)
  · rw [ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit18_1.1 (by norm_num) (by norm_num)
  · rw [ea_S5.1, poly3_eq _ _ _ (5 / 2) _ log_4s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit18_5.1 (by norm_num) (by norm_num)
  · rw [ea_S1.2, ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit18_1.1 B_fit18_1.2 d1_bd.1 d1_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [ea_S1.2, ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit18_1.1 B_fit18_1.2 d1_bd.1 d1_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [ea_S5.2, ea_S5.1, poly3_eq _ _ _ (5 / 2) _ log_4s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit18_5.1 B_fit18_5.2 d5_bd.1 d5_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · apply concl_neg; norm_num; nlinarith

/-- Without the redshift of the farthest source: that source placed at the middle one (`1 + z = 2√2`); the cubic of `fit_direction_h19` matches both distinct sources. -/
theorem fit_direction_h12 : necessity% Checked.Cosmography.B1Fit.fit_direction 12 := by
  obtain ⟨o53, o31, o10, p5, p3⟩ := ea_ord
  obtain ⟨l1, l2⟩ := log10_bd
  obtain ⟨m1, m2⟩ := lam_bd
  obtain ⟨n1, n2⟩ := log2L_bd
  obtain ⟨hp, hd, hH₀, hH⟩ := ea_hyps _ p3
  refine ⟨1, by norm_num, le_rfl, ea, tE (2 * √2), tE (2 * √2), _, 1, le_rfl, o31, o10, hp, hd, hH₀, hH, ea_S1.1, ea_S3.1,
    (8:ℝ), (-21 / 4 : ℝ), 1.0706, 0, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit19_1.1 (by norm_num) (by norm_num)
  · rw [ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit19_3.1 (by norm_num) (by norm_num)
  · rw [ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_fit19_3.1 (by norm_num) (by norm_num)
  · rw [ea_S1.2, ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit19_1.1 B_fit19_1.2 d1_bd.1 d1_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [ea_S3.2, ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit19_3.1 B_fit19_3.2 d3_bd.1 d3_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [ea_S3.2, ea_S3.1, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_fit19_3.1 B_fit19_3.2 d3_bd.1 d3_bd.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · apply concl_neg; norm_num; nlinarith


/-- `rl19_box_unmatched` without the redshift of the middle source: that source placed at the nearest
one (`1 + z = √2`); in the Einstein–de Sitter model the box point `a₂ = 69/20`, `a₃ = 83/50` matches
the distance moduli at `√2` and `4√2` within 1/20 mag. -/
theorem rl19_box_unmatched_h11 : necessity% Checked.Cosmography.B1FitRL19.rl19_box_unmatched 11 := by
  obtain ⟨o53, o31, o10, p5, p3⟩ := ea_ord
  obtain ⟨l1, l2⟩ := log10_bd
  obtain ⟨hp, hd, hH₀, hH⟩ := ea_hyps _ p5
  refine ⟨1, by norm_num, le_rfl, ea, _, tE √2, tE √2, 1, le_trans o53 o31, le_rfl, o10, hp, hd, hH₀,
    hH, ea_S1.1, ea_S5.1, (69 / 20 : ℝ), (83 / 50 : ℝ), 0.7993, 0, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · rw [ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_rl11_1.1 (by norm_num) (by norm_num)
  · rw [ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_rl11_1.1 (by norm_num) (by norm_num)
  · rw [ea_S5.1, poly3_eq _ _ _ (5 / 2) _ log_4s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_rl11_5.1 (by norm_num) (by norm_num)
  · have h1 : |5 * Real.logb 10 (lumDistFlat ea 1 (tE √2) / logPolyDL3 (69 / 20 : ℝ) (83 / 50 : ℝ) 0.7993
        (redshift ea 1 (tE √2))) - 0| ≤ 1 / 20 := by
      rw [ea_S1.2, ea_S1.1, poly3_eq _ _ _ (1 / 2) _ log_s2]
      exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_rl11_1.1 B_rl11_1.2 d1_bd.1 d1_bd.2
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h5 : |5 * Real.logb 10 (lumDistFlat ea 1 (tE (4 * √2)) / logPolyDL3 (69 / 20 : ℝ) (83 / 50 : ℝ) 0.7993
        (redshift ea 1 (tE (4 * √2)))) - 0| ≤ 1 / 20 := by
      rw [ea_S5.2, ea_S5.1, poly3_eq _ _ _ (5 / 2) _ log_4s2]
      exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_rl11_5.1 B_rl11_5.2 d5_bd.1 d5_bd.2
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨h1, h1, h5⟩


/-! ## Curved Lusso et al. 2019 pair without `Ω ≤ 1`: the flat (`K = 0`) model at `Ω = 100` -/

theorem inner_pos1 (Ω v : ℝ) (hΩ : 1 ≤ Ω) (hv : 0 ≤ v) (hv1 : v ≤ 1) : 0 < Ω + (1 - Ω) * v ^ 6 := by
  have h6 : v ^ 6 ≤ 1 := pow_le_one₀ hv hv1
  nlinarith

theorem piece_lo (Ω p q c : ℝ) (hΩ : 1 ≤ Ω) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1) (hc : 0 < c)
    (h : Ω + (1 - Ω) * p ^ 6 ≤ (2 / c) ^ 2) :
    (q - p) * c ≤ ∫ v in p..q, 2 / √(Ω + (1 - Ω) * v ^ 6) := by
  obtain ⟨hA, -⟩ := int_piece Ω p q hΩ hp hpq hq
  have hR := inner_pos1 Ω p hΩ hp (le_trans hpq hq)
  have hs : √(Ω + (1 - Ω) * p ^ 6) ≤ 2 / c := by
    rw [show 2 / c = √((2 / c) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt h
  have hcg : c ≤ 2 / √(Ω + (1 - Ω) * p ^ 6) := by
    rw [le_div_iff₀ (Real.sqrt_pos.2 hR)]
    calc c * √(Ω + (1 - Ω) * p ^ 6) ≤ c * (2 / c) := mul_le_mul_of_nonneg_left hs hc.le
      _ = 2 := by field_simp
  nlinarith

theorem piece_up (Ω p q c : ℝ) (hΩ : 1 ≤ Ω) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1) (hc : 0 < c)
    (h : (2 / c) ^ 2 ≤ Ω + (1 - Ω) * q ^ 6) :
    ∫ v in p..q, 2 / √(Ω + (1 - Ω) * v ^ 6) ≤ (q - p) * c := by
  obtain ⟨-, hB⟩ := int_piece Ω p q hΩ hp hpq hq
  have hs : 2 / c ≤ √(Ω + (1 - Ω) * q ^ 6) := by
    rw [show 2 / c = √((2 / c) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt h
  have hR : 0 < √(Ω + (1 - Ω) * q ^ 6) := lt_of_lt_of_le (by positivity) hs
  have hcg : 2 / √(Ω + (1 - Ω) * q ^ 6) ≤ c := by
    rw [div_le_iff₀ hR]
    calc 2 = c * (2 / c) := by field_simp
      _ ≤ c * √(Ω + (1 - Ω) * q ^ 6) := mul_le_mul_of_nonneg_left hs hc.le
  nlinarith

set_option maxHeartbeats 4000000 in
/-- At `Ω = 100`: `J₅ ≤ 1.318 J₃` with `J_Z = ∫_{1/√Z}^1 g` (twenty-step lower sum of `J₃`,
four-step upper sum of the rest). -/
theorem J53_100 :
    let J3 := ∫ v in √(1 / (2 * √2))..1, 2 / √(100 + (1 - 100) * v ^ 6)
    let J5 := ∫ v in √(1 / (4 * √2))..1, 2 / √(100 + (1 - 100) * v ^ 6)
    0 < J3 ∧ J5 ≤ 1.318 * J3 := by
  intro J3 J5
  obtain ⟨a3, b3⟩ := v3_bd
  obtain ⟨a5, b5⟩ := v5_bd
  have b3' : √(1 / (2 * √2)) ≤ (5947 / 10000 : ℝ) := le_of_le_of_eq b3 (by norm_num)
  have a5' : (1051 / 2500 : ℝ) ≤ √(1 / (4 * √2)) := le_of_eq_of_le (by norm_num) a5
  have P0 := piece_lo 100 (5947 / 10000 : ℝ) (3171 / 5000 : ℝ) (12783 / 62500 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have P1 := piece_lo 100 (3171 / 5000 : ℝ) (6717 / 10000 : ℝ) (20677 / 100000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have P2 := piece_lo 100 (6717 / 10000 : ℝ) (442 / 625 : ℝ) (209763 / 1000000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have P3 := piece_lo 100 (442 / 625 : ℝ) (3703 / 5000 : ℝ) (53417 / 250000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have P4 := piece_lo 100 (3703 / 5000 : ℝ) (193 / 250 : ℝ) (43731 / 200000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have P5 := piece_lo 100 (193 / 250 : ℝ) (4007 / 5000 : ℝ) (224957 / 1000000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have P6 := piece_lo 100 (4007 / 5000 : ℝ) (518 / 625 : ℝ) (232851 / 1000000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have P7 := piece_lo 100 (518 / 625 : ℝ) (8541 / 10000 : ℝ) (242691 / 1000000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have P8 := piece_lo 100 (8541 / 10000 : ℝ) (4387 / 5000 : ℝ) (31861 / 125000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have P9 := piece_lo 100 (4387 / 5000 : ℝ) (8987 / 10000 : ℝ) (27009 / 100000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have P10 := piece_lo 100 (8987 / 10000 : ℝ) (9179 / 10000 : ℝ) (4518 / 15625 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have P11 := piece_lo 100 (9179 / 10000 : ℝ) (1169 / 1250 : ℝ) (78289 / 250000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have P12 := piece_lo 100 (1169 / 1250 : ℝ) (594 / 625 : ℝ) (43021 / 125000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have P13 := piece_lo 100 (594 / 625 : ℝ) (1927 / 2000 : ℝ) (192301 / 500000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have P14 := piece_lo 100 (1927 / 2000 : ℝ) (9747 / 10000 : ℝ) (54821 / 125000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have P15 := piece_lo 100 (9747 / 10000 : ℝ) (4919 / 5000 : ℝ) (514529 / 1000000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have P16 := piece_lo 100 (4919 / 5000 : ℝ) (9909 / 10000 : ℝ) (624957 / 1000000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have P17 := piece_lo 100 (9909 / 10000 : ℝ) (9959 / 10000 : ℝ) (398919 / 500000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have P18 := piece_lo 100 (9959 / 10000 : ℝ) (999 / 1000 : ℝ) (1082969 / 1000000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have P19 := piece_lo 100 (999 / 1000 : ℝ) (1 / 1 : ℝ) (1584849 / 1000000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have S0 := int_split 100 (5947 / 10000 : ℝ) (3171 / 5000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have ea_S1 := int_split 100 (3171 / 5000 : ℝ) (6717 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have S2 := int_split 100 (6717 / 10000 : ℝ) (442 / 625 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have ea_S3 := int_split 100 (442 / 625 : ℝ) (3703 / 5000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have S4 := int_split 100 (3703 / 5000 : ℝ) (193 / 250 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have ea_S5 := int_split 100 (193 / 250 : ℝ) (4007 / 5000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have S6 := int_split 100 (4007 / 5000 : ℝ) (518 / 625 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have S7 := int_split 100 (518 / 625 : ℝ) (8541 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have S8 := int_split 100 (8541 / 10000 : ℝ) (4387 / 5000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have S9 := int_split 100 (4387 / 5000 : ℝ) (8987 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have S10 := int_split 100 (8987 / 10000 : ℝ) (9179 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have S11 := int_split 100 (9179 / 10000 : ℝ) (1169 / 1250 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have S12 := int_split 100 (1169 / 1250 : ℝ) (594 / 625 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have S13 := int_split 100 (594 / 625 : ℝ) (1927 / 2000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have S14 := int_split 100 (1927 / 2000 : ℝ) (9747 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have S15 := int_split 100 (9747 / 10000 : ℝ) (4919 / 5000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have S16 := int_split 100 (4919 / 5000 : ℝ) (9909 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have S17 := int_split 100 (9909 / 10000 : ℝ) (9959 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have S18 := int_split 100 (9959 / 10000 : ℝ) (999 / 1000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have U0 := piece_up 100 (1051 / 2500 : ℝ) (23 / 50 : ℝ) (40189 / 200000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have U1 := piece_up 100 (23 / 50 : ℝ) (1 / 2 : ℝ) (100783 / 500000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have U2 := piece_up 100 (1 / 2 : ℝ) (27 / 50 : ℝ) (202501 / 1000000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have U3 := piece_up 100 (27 / 50 : ℝ) (5947 / 10000 : ℝ) (204529 / 1000000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have T0 := int_split 100 (1051 / 2500 : ℝ) (23 / 50 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have T1 := int_split 100 (23 / 50 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have T2 := int_split 100 (1 / 2 : ℝ) (27 / 50 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have T3 := int_split 100 (27 / 50 : ℝ) (5947 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hΩ : (1:ℝ) ≤ 100 := by norm_num
  have e3 := int_split 100 (√(1 / (2 * √2))) (5947 / 10000) hΩ (by linarith) b3' (by norm_num)
  have e5 := int_split 100 (1051 / 2500) (√(1 / (4 * √2))) hΩ (by norm_num) a5' (by linarith)
  obtain ⟨z3, -⟩ := int_piece 100 (√(1 / (2 * √2))) (5947 / 10000) hΩ (by linarith) b3' (by norm_num)
  obtain ⟨z5, -⟩ := int_piece 100 (1051 / 2500) (√(1 / (4 * √2))) hΩ (by norm_num) a5' (by linarith)
  have g3 := g_ge 100 (√(1 / (2 * √2))) hΩ (by linarith) (by linarith)
  have g5 := g_ge 100 (1051 / 2500) hΩ (by norm_num) (by norm_num)
  have hs : 0 < 2 / √(100:ℝ) := by positivity
  have n3 : 0 ≤ ((5947 / 10000 : ℝ) - √(1 / (2 * √2))) * (2 / √(100 + (1 - 100) * √(1 / (2 * √2)) ^ 6)) :=
    mul_nonneg (by linarith) (by linarith)
  have n5 : 0 ≤ (√(1 / (4 * √2)) - (1051 / 2500 : ℝ)) * (2 / √(100 + (1 - 100) * (1051 / 2500 : ℝ) ^ 6)) :=
    mul_nonneg (by linarith) (by linarith)
  constructor
  · show 0 < ∫ v in √(1 / (2 * √2))..1, 2 / √(100 + (1 - 100) * v ^ 6)
    linarith
  · show ∫ v in √(1 / (4 * √2))..1, 2 / √(100 + (1 - 100) * v ^ 6) ≤
      1.318 * ∫ v in √(1 / (2 * √2))..1, 2 / √(100 + (1 - 100) * v ^ 6)
    linarith


/-- The `Ω = 100` model with sources at `1 + z = 2√2` and `4√2`. -/
theorem data_100 :
    tS 100 (4 * √2) ≤ tS 100 (2 * √2) ∧ tS 100 (2 * √2) ≤ tO 100 ∧
      (∀ s ∈ Set.Icc (tS 100 (4 * √2)) (tO 100), 0 < sa s) ∧
      (∀ s ∈ Set.Icc (tS 100 (4 * √2)) (tO 100), DifferentiableAt ℝ sa s) ∧ 0 < hubble sa (tO 100) ∧
      (∀ s ∈ Set.Icc (tS 100 (4 * √2)) (tO 100),
        hubble sa s = hubble sa (tO 100) * √(100 * (1 + redshift sa (tO 100) s) ^ 3 + 1 - 100)) ∧
      redshift sa (tO 100) (tS 100 (2 * √2)) = 2 * √2 - 1 ∧
      redshift sa (tO 100) (tS 100 (4 * √2)) = 4 * √2 - 1 := by
  have hΩ : (1:ℝ) < 100 := by norm_num
  obtain ⟨s1, -⟩ := sqrt2_bd
  obtain ⟨h0, h1, hc⟩ := tO_props 100 hΩ
  obtain ⟨ht5, -, hz5⟩ := tS_props 100 (4 * √2) hΩ (by linarith)
  obtain ⟨-, h3O, hz3⟩ := tS_props 100 (2 * √2) hΩ (by linarith)
  obtain ⟨hp, hd, hH₀, hH⟩ := sa_hyps 100 (tO 100) (tS 100 (4 * √2)) h0 h1 hc ht5
  exact ⟨tS_anti 100 _ _ hΩ (by linarith) (by linarith), h3O, hp, hd, hH₀, hH, hz3, hz5⟩

/-- At `Ω = 100`, with quartic coefficients whose brackets are positive, the ratio of the two
distance ratios is at most `2 · 1.318 · B₃/B₅`. -/
theorem ratio_100 (a₂ a₃ a₄ : ℝ)
    (hB3 : 0 < Bq a₂ a₃ a₄ (3 / 2 * (Real.log 2 / Real.log 10)))
    (hB5 : 0 < Bq a₂ a₃ a₄ (5 / 2 * (Real.log 2 / Real.log 10))) :
    let x5 := lumDistFlat sa (tO 100) (tS 100 (4 * √2)) /
      logPolyDL4 a₂ a₃ a₄ 1 (redshift sa (tO 100) (tS 100 (4 * √2)))
    let x3 := lumDistFlat sa (tO 100) (tS 100 (2 * √2)) /
      logPolyDL4 a₂ a₃ a₄ 1 (redshift sa (tO 100) (tS 100 (2 * √2)))
    0 < x5 ∧ 0 < x3 ∧ x5 / x3 ≤ 2 * 1.318 * Bq a₂ a₃ a₄ (3 / 2 * (Real.log 2 / Real.log 10)) /
      Bq a₂ a₃ a₄ (5 / 2 * (Real.log 2 / Real.log 10)) := by
  intro x5 x3
  obtain ⟨-, -, -, -, hH₀, -, hz3, hz5⟩ := data_100
  obtain ⟨s1, -⟩ := sqrt2_bd
  have hΩ : (1:ℝ) < 100 := by norm_num
  obtain ⟨hJ3, hJ53⟩ := J53_100
  have hl10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have e5 : x5 = 4 * √2 / hubble sa (tO 100) *
      (∫ v in √(1 / (4 * √2))..1, 2 / √(100 + (1 - 100) * v ^ 6)) /
      (Real.log 10 * Bq a₂ a₃ a₄ (5 / 2 * (Real.log 2 / Real.log 10))) := by
    simp only [x5]; rw [hz5, poly4_eq _ _ _ _ _ log_4s2, sa_dL 100 _ hΩ (by linarith)]
  have e3 : x3 = 2 * √2 / hubble sa (tO 100) *
      (∫ v in √(1 / (2 * √2))..1, 2 / √(100 + (1 - 100) * v ^ 6)) /
      (Real.log 10 * Bq a₂ a₃ a₄ (3 / 2 * (Real.log 2 / Real.log 10))) := by
    simp only [x3]; rw [hz3, poly4_eq _ _ _ _ _ log_2s2, sa_dL 100 _ hΩ (by linarith)]
  have hJ5 : 0 < ∫ v in √(1 / (4 * √2))..1, 2 / √(100 + (1 - 100) * v ^ 6) := by
    obtain ⟨a5, b5⟩ := v5_bd
    obtain ⟨a3, b3⟩ := v3_bd
    have hs5 := int_split 100 (√(1 / (4 * √2))) (√(1 / (2 * √2))) (by norm_num) (by linarith)
      (by linarith) (by linarith)
    obtain ⟨hK, -⟩ := int_piece 100 (√(1 / (4 * √2))) (√(1 / (2 * √2))) (by norm_num) (by linarith)
      (by linarith) (by linarith)
    have hg := g_ge 100 (√(1 / (4 * √2))) (by norm_num) (by linarith) (by linarith)
    have : 0 < 2 / √(100:ℝ) := by positivity
    have hm : 0 ≤ (√(1 / (2 * √2)) - √(1 / (4 * √2))) * (2 / √(100 + (1 - 100) * √(1 / (4 * √2)) ^ 6)) :=
      mul_nonneg (by linarith) (by linarith)
    rw [hs5]; linarith
  set J3 := ∫ v in √(1 / (2 * √2))..1, 2 / √(100 + (1 - 100) * v ^ 6)
  set J5 := ∫ v in √(1 / (4 * √2))..1, 2 / √(100 + (1 - 100) * v ^ 6)
  set B3 := Bq a₂ a₃ a₄ (3 / 2 * (Real.log 2 / Real.log 10))
  set B5 := Bq a₂ a₃ a₄ (5 / 2 * (Real.log 2 / Real.log 10))
  set H := hubble sa (tO 100)
  have hs : 0 < √2 := by positivity
  have hx5 : 0 < x5 := by rw [e5]; positivity
  have hx3 : 0 < x3 := by rw [e3]; positivity
  refine ⟨hx5, hx3, ?_⟩
  have hy : x5 / x3 = 2 * J5 * B3 / (J3 * B5) := by
    rw [e5, e3]; field_simp; ring
  rw [hy, div_le_div_iff₀ (by positivity) hB5]
  have : 2 * J5 * B3 * B5 ≤ 2 * (1.318 * J3) * B3 * B5 := by gcongr
  nlinarith

theorem lumDist_zero (a : ℝ → ℝ) (t₀ t : ℝ) : lumDist 0 a t₀ t = lumDistFlat a t₀ t := by
  unfold lumDist lumDistFlat transverse; simp

theorem omega0_zero (a : ℝ → ℝ) (t₀ : ℝ) : omega0 0 a t₀ = 1 := by unfold omega0; simp

/-- The curved law at `K = 0` is the flat law. -/
theorem curved_hH (Ω : ℝ) (a : ℝ → ℝ) (t₅ t₀ : ℝ)
    (hH : ∀ s ∈ Set.Icc t₅ t₀, hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω)) :
    ∀ s ∈ Set.Icc t₅ t₀, hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3
        + (1 - omega0 0 a t₀) * (1 + redshift a t₀ s) ^ 2 + omega0 0 a t₀ - Ω) := by
  intro s hs
  rw [hH s hs, omega0_zero]; ring_nf

/-- `l19_sq_curved` without `Ω ≤ 1`: the flat model (`K = 0`, total density one) at `Ω = 100`; the residual
of the central fit grows by at most 1/4 mag between `1 + z = 2√2` and `4√2`. -/
theorem l19_sq_curved_h2 : necessity% Checked.Cosmography.B1L19Curved.l19_sq_curved 2 := by
  obtain ⟨h53, h3O, hp, hd, hH₀, hH, hz3, hz5⟩ := data_100
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  have q4 := pow_le_pow_left₀ (by norm_num) l1 4
  have q4' := pow_le_pow_left₀ (by linarith) l2 4
  have hB3 : 0 < Bq 3.075 4.466 (-3.716) (3 / 2 * lam) := by unfold Bq; ring_nf; ring_nf at q2 q2' q3 q3' q4 q4'; linarith
  have hB5 : 0 < Bq 3.075 4.466 (-3.716) (5 / 2 * lam) := by unfold Bq; ring_nf; ring_nf at q2 q2' q3 q3' q4 q4'; linarith
  obtain ⟨hx5, hx3, hr⟩ := ratio_100 3.075 4.466 (-3.716) hB3 hB5
  refine ⟨100, 0, by norm_num, sa, _, _, tO 100, h53, h3O, hp, hd, hH₀, by rw [omega0_zero],
    by rw [omega0_zero]; norm_num, curved_hH 100 sa _ _ hH, hz3, hz5, 1, one_pos, ?_⟩
  rw [lumDist_zero, lumDist_zero, not_lt, logb_div' _ _ hx5 hx3]
  have hb : 2 * 1.318 * Bq 3.075 4.466 (-3.716) (3 / 2 * lam) / Bq 3.075 4.466 (-3.716) (5 / 2 * lam)
      ≤ 1.1 := by
    rw [div_le_iff₀ hB5]; unfold Bq; ring_nf; ring_nf at q2 q2' q3 q3' q4 q4'; linarith
  have hy := le_trans hr hb
  have hpow : (_ : ℝ) ^ 100 ≤ (10:ℝ) ^ 5 :=
    le_trans (pow_le_pow_left₀ (div_pos hx5 hx3).le hy 100) (by norm_num)
  have := logb_le_of_pow _ 5 100 (div_pos hx5 hx3) hpow (by norm_num)
  norm_num at this ⊢; linarith

/-- `l19_sqg_curved` without `Ω ≤ 1`: the same model; the SNe + GRB + quasar central fit's residual grows by
at most 3/20 mag. -/
theorem l19_sqg_curved_h2 : necessity% Checked.Cosmography.B1L19Curved.l19_sqg_curved 2 := by
  obtain ⟨h53, h3O, hp, hd, hH₀, hH, hz3, hz5⟩ := data_100
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  have q4 := pow_le_pow_left₀ (by norm_num) l1 4
  have q4' := pow_le_pow_left₀ (by linarith) l2 4
  have hB3 : 0 < Bq 3.205 3.564 (-2.510) (3 / 2 * lam) := by unfold Bq; ring_nf; ring_nf at q2 q2' q3 q3' q4 q4'; linarith
  have hB5 : 0 < Bq 3.205 3.564 (-2.510) (5 / 2 * lam) := by unfold Bq; ring_nf; ring_nf at q2 q2' q3 q3' q4 q4'; linarith
  obtain ⟨hx5, hx3, hr⟩ := ratio_100 3.205 3.564 (-2.510) hB3 hB5
  refine ⟨100, 0, by norm_num, sa, _, _, tO 100, h53, h3O, hp, hd, hH₀, by rw [omega0_zero],
    by rw [omega0_zero]; norm_num, curved_hH 100 sa _ _ hH, hz3, hz5, 1, one_pos, ?_⟩
  rw [lumDist_zero, lumDist_zero, not_lt, logb_div' _ _ hx5 hx3]
  have hb : 2 * 1.318 * Bq 3.205 3.564 (-2.510) (3 / 2 * lam) / Bq 3.205 3.564 (-2.510) (5 / 2 * lam)
      ≤ 1.07 := by
    rw [div_le_iff₀ hB5]; unfold Bq; ring_nf; ring_nf at q2 q2' q3 q3' q4 q4'; linarith
  have hy := le_trans hr hb
  have hpow : (_ : ℝ) ^ 100 ≤ (10:ℝ) ^ 3 :=
    le_trans (pow_le_pow_left₀ (div_pos hx5 hx3).le hy 100) (by norm_num)
  have := logb_le_of_pow _ 3 100 (div_pos hx5 hx3) hpow (by norm_num)
  norm_num at this ⊢; linarith

end Checked.Trust.NCAR
