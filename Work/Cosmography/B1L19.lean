import Checked.Cosmography.B1Fit
import Work.Cosmography.B1L19Certs

/-!
# B1, fourth order: between z ≈ 1.8 and z ≈ 4.7 the quasar-driven Lusso et al. 2019 fitted curves rise less than the exact distance of every flat ΛCDM model with Ω ∈ [0, 1]

**Question (STATE "B1", "Not yet": the Lusso et al. 2019/2020 fourth-order fits).**
Lusso et al. 2019 (A&A 628, L4; arXiv:1907.07692v4, Eq. (7)) fit
`D_L = k ln(10)(c/H₀)(x + a₂x² + a₃x³ + a₄x⁴)`, `x = log₁₀(1+z)`, with a free normalisation `k`
per sample, to supernovae, quasars and gamma-ray bursts, and report the fits in their Table 2
(SNe + quasars + GRBs: `a₂ = 3.205`, `a₃ = 3.564`, `a₄ = −2.510`; SNe + quasars: `3.075`, `4.466`,
`−3.716`; each with asymmetric uncertainties; the caption states neither the confidence level nor
whether the values are medians — "1σ" below is the natural reading, not printed; Table 2 is
identical in arXiv v1–v4, blind second reading `runs/2026-11-04T1228Z/second_reading_l19.md`).
They measure the tension with ΛCDM as the distance of these coefficients from the Taylor values of
their Eq. (8). The critique (Yang et al. 2020, arXiv:1911.01681; Banerjee et al. 2021,
arXiv:2009.04109) is that the truncated series represents exact ΛCDM badly at high redshift, so
coefficient distances from the Taylor point are not evidence against ΛCDM.

This file compares the fitted *curves* with the *exact* flat ΛCDM distance, not with the Taylor
coefficients, so truncation of the ΛCDM side cannot enter: the normalisation (`k`, `H₀`, any
magnitude offset) cancels in the difference of distance moduli between two redshifts of the same
sample. The two redshifts `1 + z = 2√2` and `1 + z = 4√2` lie inside the quasar range.

**Statements (frozen before proof).**
* `l19_sq_central`, `l19_sqg_central`: at the printed central coefficients, for every Ω ∈ [0, 1]
  and every scale factor obeying `H = H₀√(Ω(1+z)³ + 1 − Ω)` back to the farther source, the exact
  distance modulus rises between the two redshifts by more than the fitted quartic's does, by more
  than 7/20 mag (SNe + quasars) and 3/10 mag (SNe + quasars + GRBs).
* `l19_sq_box`, `l19_sqg_box`: the same with margin 0 for *every* quartic whose coefficients lie at
  or beyond the printed 1σ ends in the direction that brings the curve's ratio closer to the exact
  one (`a₂ ≥ 2.906`, `a₃ ≤ 5.479`, `a₄ ≤ −1.794` for SNe + quasars, the printed central value minus
  or plus one printed σ; `a₂ ≥ 3.043`, `a₃ ≤ 4.480`, `a₄ ≤ −0.915` for SNe + quasars + GRBs). This
  region contains the whole coordinate box of the printed ±1σ ranges, so the statement holds
  whatever the (unprinted) covariance; but that box is not a 68% joint region (it contains only the
  Δχ² = 1 ellipsoid, about 20% probability for three Gaussian parameters; referee §4.3).

**What this does and does not say** (referee `runs/2026-11-04T1228Z/referee_l19.md`,
STANDS-WITH-CORRECTIONS). It shows that the deviation of the central fitted curves from flat ΛCDM
is not the Taylor-truncation artefact of the critique: the curves themselves are not flat-ΛCDM
shaped between these redshifts. It is a two-redshift shape statement, not a statement about the
data, their errors or significance (linearised, the box result corresponds to only ≈ 1–1.5σ in the
ratio, far from the claimed 4σ), about quasar standardisation, or about curved models: closed ΛCDM
models reproduce the central ratio (referee §4.3(iii)). Most of the margin comes from the z ≈ 1.8 →
4.7 leg, where the quartic extrapolates over sparser data. The qualitative conclusion — the quasar
Hubble diagram prefers flat models with Ω_m near or above 1 — is in Yang et al. 2020, Khadka & Ratra
2020 and Bargiacchi et al. 2021; new here is the certified, Ω-uniform, normalisation-free form.

Positivity of the polynomial distance at the farther redshift is assumed in the box statements (a
negative distance has no distance modulus; `Real.logb` would silently take the absolute value);
positivity at the nearer redshift follows, and at the central values both are consequences.

Floating-point exploration (`runs/2026-11-04T1228Z/scripts/`; referee §1): the exact ratio
`d_L(4√2 − 1)/d_L(2√2 − 1)` decreases in Ω from 5.09 (Ω = 0) to 2.859 (Ω = 1, Einstein–de Sitter);
the central quartics give 2.401 (SNe + quasars) and 2.470 (+ GRBs), the box corners 2.821 and 2.829;
the SNe + GRBs fit (no quasars; `a₂ = 3.304`, `a₃ = 2.069`, `a₄ = 2.571`) gives 3.044, matched by
Ω ≈ 0.354. These floating-point numbers are not claims of the theorems.

Conventions: as `Checked.Cosmography.B1` (`c = 1`, `hubble a t = ȧ/a`,
`redshift a t₀ t = a(t₀)/a(t) − 1`, `lumDistFlat`; distance-modulus difference `5 log₁₀(d/d')`).

FROZEN (annex 40.1) in run 2026-11-04T1228Z before proof work.
-/

namespace Work.Cosmography.B1L19

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1

/-- The fourth-order log-polynomial luminosity distance of Lusso et al. 2019, Eq. (7):
`D_L = ln(10) (c/H₀) (x + a₂x² + a₃x³ + a₄x⁴)`, `x = log₁₀(1+z)`, with `c = 1` and the free
normalisation `k` absorbed into `H₀`. -/
noncomputable def logPolyDL4 (a₂ a₃ a₄ H₀ z : ℝ) : ℝ :=
  Real.log 10 / H₀ *
    (Real.logb 10 (1 + z) + a₂ * Real.logb 10 (1 + z) ^ 2 + a₃ * Real.logb 10 (1 + z) ^ 3
      + a₄ * Real.logb 10 (1 + z) ^ 4)

/-! ## Proof tools (not part of the frozen statements)

The two distances are reduced to `J₃ = ∫_{w₃}^1 gL Ω`, `J₅ = ∫_{w₅}^1 gL Ω` (`w = (1+z)^{-1/2}`),
whose ratio is bounded by the generated certificates (`Work.Cosmography.B1L19Certs.ratio_bound`:
`d_L(4√2 − 1)/d_L(2√2 − 1) = 2J₅/J₃ ≥ 2.84` for every `Ω ∈ [0, 1]`); the polynomial side is exact
algebra with `log₁₀ 2 ∈ [0.30101, 0.30105]`. -/

open Checked.Cosmography.B1Fit

lemma log_ten_le' : Real.log 10 ≤ (10 * 0.6931471808 - 24 / 1024) / 3 := by
  have h1 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1000 / 1024 by norm_num)
  have h2 : Real.log (1000 / 1024) = 3 * Real.log 10 - 10 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (1000:ℝ) = 10 ^ 3 by norm_num, show (1024:ℝ) = 2 ^ 10 by norm_num,
      Real.log_pow, Real.log_pow]; push_cast; ring
  rw [h2] at h1
  linarith [Real.log_two_lt_d9]

lemma L_bounds : (30101 / 100000 : ℝ) ≤ Real.log 2 / Real.log 10 ∧
    Real.log 2 / Real.log 10 ≤ 30105 / 100000 := by
  have hl0 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have h1 := log_ten_ge
  have h2 := log_ten_le'
  have h3 := Real.log_two_gt_d9
  have h4 := Real.log_two_lt_d9
  constructor
  · rw [le_div_iff₀ hl0]; nlinarith
  · rw [div_le_iff₀ hl0]; nlinarith

lemma lp4_eq (a₂ a₃ a₄ H x z : ℝ) (hx : Real.logb 10 (1 + z) = x) :
    logPolyDL4 a₂ a₃ a₄ H z = Real.log 10 / H * (x + a₂ * x ^ 2 + a₃ * x ^ 3 + a₄ * x ^ 4) := by
  unfold logPolyDL4; rw [hx]

lemma x3_eq : Real.logb 10 (1 + (2 * √2 - 1)) = 3 / 2 * (Real.log 2 / Real.log 10) := by
  rw [show (1:ℝ) + (2 * √2 - 1) = 2 * √2 by ring]
  unfold Real.logb
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_sqrt (by norm_num)]; ring

lemma x5_eq : Real.logb 10 (1 + (4 * √2 - 1)) = 5 / 2 * (Real.log 2 / Real.log 10) := by
  rw [show (1:ℝ) + (4 * √2 - 1) = 4 * √2 by ring]
  unfold Real.logb
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_sqrt (by norm_num),
    show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring

/-- The residual difference is at least `5 log₁₀(2.84 · P(x₃)/P(x₅))`. -/
lemma delta_ge (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1) (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)
    (a₂ a₃ a₄ H : ℝ) (hHp : 0 < H) (x₃ x₅ : ℝ)
    (hx₃ : Real.logb 10 (1 + (2 * √2 - 1)) = x₃) (hx₅ : Real.logb 10 (1 + (4 * √2 - 1)) = x₅)
    (hQ3 : 0 < x₃ + a₂ * x₃ ^ 2 + a₃ * x₃ ^ 3 + a₄ * x₃ ^ 4)
    (hQ5 : 0 < x₅ + a₂ * x₅ ^ 2 + a₃ * x₅ ^ 3 + a₄ * x₅ ^ 4) :
    5 * Real.logb 10 (284 / 100 * (x₃ + a₂ * x₃ ^ 2 + a₃ * x₃ ^ 3 + a₄ * x₃ ^ 4)
        / (x₅ + a₂ * x₅ ^ 2 + a₃ * x₅ ^ 3 + a₄ * x₅ ^ 4))
      ≤ 5 * Real.logb 10 (lumDistFlat a t₀ t₅ / logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₅))
        - 5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₃)) := by
  have h₅₀ : t₅ ≤ t₀ := le_trans h₅₃ h₃₀
  have hsub3 : Set.Icc t₃ t₀ ⊆ Set.Icc t₅ t₀ := Set.Icc_subset_Icc_left h₅₃
  have hbr3 := lumDistFlat_flatLCDM Ω hΩ₀ hΩ₁ a t₃ t₀ h₃₀ (fun s hs => hpos s (hsub3 hs))
    (fun s hs => hdiff s (hsub3 hs)) hH₀ (fun s hs => hH s (hsub3 hs))
  have hbr5 := lumDistFlat_flatLCDM Ω hΩ₀ hΩ₁ a t₅ t₀ h₅₀ hpos hdiff hH₀ hH
  have ha₀ : 0 < a t₀ := hpos t₀ ⟨h₅₀, le_rfl⟩
  have ha3 : 0 < a t₃ := hpos t₃ ⟨h₅₃, h₃₀⟩
  have ha5 : 0 < a t₅ := hpos t₅ ⟨le_rfl, h₅₀⟩
  have es3 : (1:ℝ) + (2 * √2 - 1) = 2 * √2 := by ring
  have es5 : (1:ℝ) + (4 * √2 - 1) = 4 * √2 := by ring
  rw [ratio_of_z a t₃ t₀ _ ha3 ha₀ hz₃, es3, hz₃, es3] at hbr3
  rw [ratio_of_z a t₅ t₀ _ ha5 ha₀ hz₅, es5, hz₅, es5] at hbr5
  change lumDistFlat a t₀ t₃ = 2 * √2 / hubble a t₀ * ∫ v in √(1 / (2 * √2))..1, gL Ω v at hbr3
  change lumDistFlat a t₀ t₅ = 4 * √2 / hubble a t₀ * ∫ v in √(1 / (4 * √2))..1, gL Ω v at hbr5
  set J3 := ∫ v in √(1 / (2 * √2))..1, gL Ω v with hJ3
  set J5 := ∫ v in √(1 / (4 * √2))..1, gL Ω v with hJ5
  set H₀ := hubble a t₀ with hH₀def
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  have hq2 : 0 < √2 := by linarith
  have hs3 : 1 < 2 * √2 := by linarith
  have hs5 : 1 < 4 * √2 := by linarith
  obtain ⟨hw3p, hw3⟩ := w_lt_one _ hs3
  obtain ⟨hw5p, hw5⟩ := w_lt_one _ hs5
  have hJ3p : 0 < J3 := Jpos Ω _ hΩ₀ hΩ₁ hw3p hw3
  have hJ5p : 0 < J5 := Jpos Ω _ hΩ₀ hΩ₁ hw5p hw5
  obtain ⟨wb3u, -⟩ := wb (2 * √2) (148651 / 250000) (594603 / 1000000) (by positivity)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  obtain ⟨-, wb5l⟩ := wb (4 * √2) (420449 / 1000000) (13139 / 31250) (by positivity)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  have hJ3u : J3 ≤ ∫ v in (594603 / 1000000 : ℝ)..1, gL Ω v :=
    J_shift Ω hΩ₀ hΩ₁ _ _ (by norm_num) wb3u hw3.le
  have hJ5l : ∫ v in (420449 / 1000000 : ℝ)..1, gL Ω v ≤ J5 :=
    J_shift Ω hΩ₀ hΩ₁ _ _ hw5p wb5l (by norm_num)
  have hrat := Work.Cosmography.B1L19Certs.ratio_bound Ω hΩ₀ hΩ₁
  have hJ : 284 / 100 ≤ 2 * J5 / J3 := by
    rw [le_div_iff₀ hJ3p]; linarith
  set Q3 := x₃ + a₂ * x₃ ^ 2 + a₃ * x₃ ^ 3 + a₄ * x₃ ^ 4 with hQ3def
  set Q5 := x₅ + a₂ * x₅ ^ 2 + a₃ * x₅ ^ 3 + a₄ * x₅ ^ 4 with hQ5def
  have hl0 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  rw [hz₃, hz₅, lp4_eq a₂ a₃ a₄ H x₃ _ hx₃, lp4_eq a₂ a₃ a₄ H x₅ _ hx₅, hbr3, hbr5]
  have hX3 : 0 < 2 * √2 / H₀ * J3 / (Real.log 10 / H * Q3) := by positivity
  have hX5 : 0 < 4 * √2 / H₀ * J5 / (Real.log 10 / H * Q5) := by positivity
  have e : 5 * Real.logb 10 (4 * √2 / H₀ * J5 / (Real.log 10 / H * Q5))
      - 5 * Real.logb 10 (2 * √2 / H₀ * J3 / (Real.log 10 / H * Q3))
      = 5 * Real.logb 10 ((4 * √2 / H₀ * J5 / (Real.log 10 / H * Q5))
          / (2 * √2 / H₀ * J3 / (Real.log 10 / H * Q3))) := by
    rw [Real.logb_div hX5.ne' hX3.ne']; ring
  have key : (4 * √2 / H₀ * J5 / (Real.log 10 / H * Q5))
      / (2 * √2 / H₀ * J3 / (Real.log 10 / H * Q3)) = 2 * J5 / J3 * (Q3 / Q5) := by
    field_simp; ring
  rw [e, key]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
  rw [show 284 / 100 * Q3 / Q5 = 284 / 100 * (Q3 / Q5) by ring]
  exact mul_le_mul_of_nonneg_right hJ (by positivity)

lemma poly_box (L a₂ a₃ a₄ b₂ b₃ b₄ : ℝ) (hL1 : 30101 / 100000 ≤ L) (hL2 : L ≤ 30105 / 100000)
    (ha₂ : b₂ ≤ a₂) (ha₃ : a₃ ≤ b₃) (ha₄ : a₄ ≤ b₄)
    (hb : 0 < 176 / 100 + 14 / 100 * b₂ * (30101 / 100000) - 604 / 100 * b₃ * (30105 / 100000) ^ 2
      - 24685 / 1000 * b₄ * (30101 / 100000) ^ 3)
    (hb₃ : 0 ≤ b₃) (hb₄ : b₄ ≤ 0) (hb₂ : 0 ≤ b₂) :
    5 / 2 * L + a₂ * (5 / 2 * L) ^ 2 + a₃ * (5 / 2 * L) ^ 3 + a₄ * (5 / 2 * L) ^ 4
      < 284 / 100 * (3 / 2 * L + a₂ * (3 / 2 * L) ^ 2 + a₃ * (3 / 2 * L) ^ 3 + a₄ * (3 / 2 * L) ^ 4) := by
  have hL0 : 0 < L := by linarith
  have p1 : b₂ * L ≤ a₂ * L := mul_le_mul_of_nonneg_right ha₂ hL0.le
  have p2 : a₃ * L ^ 2 ≤ b₃ * L ^ 2 := mul_le_mul_of_nonneg_right ha₃ (by positivity)
  have p3 : a₄ * L ^ 3 ≤ b₄ * L ^ 3 := mul_le_mul_of_nonneg_right ha₄ (by positivity)
  have l2 : L ^ 2 ≤ (30105 / 100000) ^ 2 := pow_le_pow_left₀ hL0.le hL2 2
  have l3 : (30101 / 100000) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hL1 3
  have q1 : b₂ * (30101 / 100000) ≤ b₂ * L := mul_le_mul_of_nonneg_left hL1 hb₂
  have q2 : b₃ * L ^ 2 ≤ b₃ * (30105 / 100000) ^ 2 := mul_le_mul_of_nonneg_left l2 hb₃
  have q3 : b₄ * L ^ 3 ≤ b₄ * (30101 / 100000) ^ 3 := mul_le_mul_of_nonpos_left l3 hb₄
  have hF : 0 < 176 / 100 + 14 / 100 * (a₂ * L) - 604 / 100 * (a₃ * L ^ 2)
      - 24685 / 1000 * (a₄ * L ^ 3) := by nlinarith
  have e : 284 / 100 * (3 / 2 * L + a₂ * (3 / 2 * L) ^ 2 + a₃ * (3 / 2 * L) ^ 3 + a₄ * (3 / 2 * L) ^ 4)
      - (5 / 2 * L + a₂ * (5 / 2 * L) ^ 2 + a₃ * (5 / 2 * L) ^ 3 + a₄ * (5 / 2 * L) ^ 4)
      = L * (176 / 100 + 14 / 100 * (a₂ * L) - 604 / 100 * (a₃ * L ^ 2)
      - 24685 / 1000 * (a₄ * L ^ 3)) := by ring
  nlinarith [mul_pos hL0 hF]

lemma logb_1175 : (7 / 100 : ℝ) < Real.logb 10 1.175 := by
  rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]
  have h1 : ((10:ℝ) ^ (7:ℕ)) ^ ((100:ℕ)⁻¹ : ℝ) < ((1.175:ℝ) ^ (100:ℕ)) ^ ((100:ℕ)⁻¹ : ℝ) :=
    Real.rpow_lt_rpow (by positivity) (by norm_num) (by norm_num)
  rw [Real.pow_rpow_inv_natCast (by norm_num) (by norm_num), ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num)] at h1
  convert h1 using 2; norm_num

lemma logb_1149 : (6 / 100 : ℝ) < Real.logb 10 1.149 := by
  rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]
  have h1 : ((10:ℝ) ^ (3:ℕ)) ^ ((50:ℕ)⁻¹ : ℝ) < ((1.149:ℝ) ^ (50:ℕ)) ^ ((50:ℕ)⁻¹ : ℝ) :=
    Real.rpow_lt_rpow (by positivity) (by norm_num) (by norm_num)
  rw [Real.pow_rpow_inv_natCast (by norm_num) (by norm_num), ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num)] at h1
  convert h1 using 2; norm_num

lemma poly_sq_central (L : ℝ) (hL1 : 30101 / 100000 ≤ L) (hL2 : L ≤ 30105 / 100000) :
    0 < 5 / 2 * L + 3.075 * (5 / 2 * L) ^ 2 + 4.466 * (5 / 2 * L) ^ 3 + (-3.716) * (5 / 2 * L) ^ 4 ∧
    1.175 * (5 / 2 * L + 3.075 * (5 / 2 * L) ^ 2 + 4.466 * (5 / 2 * L) ^ 3 + (-3.716) * (5 / 2 * L) ^ 4)
      < 284 / 100 * (3 / 2 * L + 3.075 * (3 / 2 * L) ^ 2 + 4.466 * (3 / 2 * L) ^ 3
        + (-3.716) * (3 / 2 * L) ^ 4) := by
  have hL0 : 0 < L := by linarith
  have l2a : (30101 / 100000) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) hL1 2
  have l2b : L ^ 2 ≤ (30105 / 100000) ^ 2 := pow_le_pow_left₀ hL0.le hL2 2
  have l3a : (30101 / 100000) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hL1 3
  have l3b : L ^ 3 ≤ (30105 / 100000) ^ 3 := pow_le_pow_left₀ hL0.le hL2 3
  constructor
  · have hG : 0 < 1 + 3.075 * (5 / 2 * L) + 4.466 * (5 / 2) ^ 2 * L ^ 2 - 3.716 * (5 / 2) ^ 3 * L ^ 3 := by
      norm_num at l2a l2b l3a l3b ⊢; linarith
    have e : 5 / 2 * L + 3.075 * (5 / 2 * L) ^ 2 + 4.466 * (5 / 2 * L) ^ 3 + (-3.716) * (5 / 2 * L) ^ 4
        = 5 / 2 * L * (1 + 3.075 * (5 / 2 * L) + 4.466 * (5 / 2) ^ 2 * L ^ 2 - 3.716 * (5 / 2) ^ 3 * L ^ 3) := by
      ring
    rw [e]; positivity
  · have hF : 0 < (284 / 100 * (3 / 2) - 1.175 * (5 / 2)) + 3.075 * (284 / 100 * (3 / 2) ^ 2 - 1.175 * (5 / 2) ^ 2) * L
        + 4.466 * (284 / 100 * (3 / 2) ^ 3 - 1.175 * (5 / 2) ^ 3) * L ^ 2
        + (-3.716) * (284 / 100 * (3 / 2) ^ 4 - 1.175 * (5 / 2) ^ 4) * L ^ 3 := by
      norm_num at l2a l2b l3a l3b ⊢; linarith
    have e : 284 / 100 * (3 / 2 * L + 3.075 * (3 / 2 * L) ^ 2 + 4.466 * (3 / 2 * L) ^ 3 + (-3.716) * (3 / 2 * L) ^ 4)
        - 1.175 * (5 / 2 * L + 3.075 * (5 / 2 * L) ^ 2 + 4.466 * (5 / 2 * L) ^ 3 + (-3.716) * (5 / 2 * L) ^ 4)
        = L * ((284 / 100 * (3 / 2) - 1.175 * (5 / 2)) + 3.075 * (284 / 100 * (3 / 2) ^ 2 - 1.175 * (5 / 2) ^ 2) * L
        + 4.466 * (284 / 100 * (3 / 2) ^ 3 - 1.175 * (5 / 2) ^ 3) * L ^ 2
        + (-3.716) * (284 / 100 * (3 / 2) ^ 4 - 1.175 * (5 / 2) ^ 4) * L ^ 3) := by ring
    nlinarith [mul_pos hL0 hF]

lemma poly_sqg_central (L : ℝ) (hL1 : 30101 / 100000 ≤ L) (hL2 : L ≤ 30105 / 100000) :
    0 < 5 / 2 * L + 3.205 * (5 / 2 * L) ^ 2 + 3.564 * (5 / 2 * L) ^ 3 + (-2.510) * (5 / 2 * L) ^ 4 ∧
    1.149 * (5 / 2 * L + 3.205 * (5 / 2 * L) ^ 2 + 3.564 * (5 / 2 * L) ^ 3 + (-2.510) * (5 / 2 * L) ^ 4)
      < 284 / 100 * (3 / 2 * L + 3.205 * (3 / 2 * L) ^ 2 + 3.564 * (3 / 2 * L) ^ 3
        + (-2.510) * (3 / 2 * L) ^ 4) := by
  have hL0 : 0 < L := by linarith
  have l2a : (30101 / 100000) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) hL1 2
  have l2b : L ^ 2 ≤ (30105 / 100000) ^ 2 := pow_le_pow_left₀ hL0.le hL2 2
  have l3a : (30101 / 100000) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hL1 3
  have l3b : L ^ 3 ≤ (30105 / 100000) ^ 3 := pow_le_pow_left₀ hL0.le hL2 3
  constructor
  · have hG : 0 < 1 + 3.205 * (5 / 2 * L) + 3.564 * (5 / 2) ^ 2 * L ^ 2 - 2.510 * (5 / 2) ^ 3 * L ^ 3 := by
      norm_num at l2a l2b l3a l3b ⊢; linarith
    have e : 5 / 2 * L + 3.205 * (5 / 2 * L) ^ 2 + 3.564 * (5 / 2 * L) ^ 3 + (-2.510) * (5 / 2 * L) ^ 4
        = 5 / 2 * L * (1 + 3.205 * (5 / 2 * L) + 3.564 * (5 / 2) ^ 2 * L ^ 2 - 2.510 * (5 / 2) ^ 3 * L ^ 3) := by
      ring
    rw [e]; positivity
  · have hF : 0 < (284 / 100 * (3 / 2) - 1.149 * (5 / 2)) + 3.205 * (284 / 100 * (3 / 2) ^ 2 - 1.149 * (5 / 2) ^ 2) * L
        + 3.564 * (284 / 100 * (3 / 2) ^ 3 - 1.149 * (5 / 2) ^ 3) * L ^ 2
        + (-2.510) * (284 / 100 * (3 / 2) ^ 4 - 1.149 * (5 / 2) ^ 4) * L ^ 3 := by
      norm_num at l2a l2b l3a l3b ⊢; linarith
    have e : 284 / 100 * (3 / 2 * L + 3.205 * (3 / 2 * L) ^ 2 + 3.564 * (3 / 2 * L) ^ 3 + (-2.510) * (3 / 2 * L) ^ 4)
        - 1.149 * (5 / 2 * L + 3.205 * (5 / 2 * L) ^ 2 + 3.564 * (5 / 2 * L) ^ 3 + (-2.510) * (5 / 2 * L) ^ 4)
        = L * ((284 / 100 * (3 / 2) - 1.149 * (5 / 2)) + 3.205 * (284 / 100 * (3 / 2) ^ 2 - 1.149 * (5 / 2) ^ 2) * L
        + 3.564 * (284 / 100 * (3 / 2) ^ 3 - 1.149 * (5 / 2) ^ 3) * L ^ 2
        + (-2.510) * (284 / 100 * (3 / 2) ^ 4 - 1.149 * (5 / 2) ^ 4) * L ^ 3) := by ring
    nlinarith [mul_pos hL0 hF]


/-- **Lusso et al. 2019, SNe + quasars, central fit.** For every `Ω ∈ [0, 1]` and every scale factor
obeying `H = H₀ √(Ω(1+z)³ + 1 − Ω)` (with `H₀ > 0`) on the whole interval back to the farther source,
with sources at `1 + z = 2√2` and `1 + z = 4√2`, and every normalisation `H > 0`, the quartic
log-polynomial distance with the printed central coefficients `a₂ = 3.075`, `a₃ = 4.466`,
`a₄ = −3.716` (Table 2) has a residual distance modulus `5 log₁₀(d_L / D_L)` against the exact luminosity
distance `d_L` (`lumDistFlat`) that is larger at the farther source: the residual at
`1 + z = 4√2` exceeds the one at `1 + z = 2√2` by more than 7/20 mag. No normalisation and no
magnitude offset can remove this difference. -/
theorem l19_sq_central (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1) (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)
    (H : ℝ) (hHp : 0 < H) :
    7 / 20 < 5 * Real.logb 10 (lumDistFlat a t₀ t₅
        / logPolyDL4 3.075 4.466 (-3.716) H (redshift a t₀ t₅))
      - 5 * Real.logb 10 (lumDistFlat a t₀ t₃
        / logPolyDL4 3.075 4.466 (-3.716) H (redshift a t₀ t₃)) := by
  obtain ⟨hL1, hL2⟩ := L_bounds
  obtain ⟨hQ5, hF⟩ := poly_sq_central _ hL1 hL2
  have hQ3 : 0 < 3 / 2 * (Real.log 2 / Real.log 10) + 3.075 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + 4.466 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + (-3.716) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4 := by linarith
  have hd := delta_ge Ω hΩ₀ hΩ₁ a t₅ t₃ t₀ h₅₃ h₃₀ hpos hdiff hH₀ hH hz₃ hz₅ 3.075 4.466 (-3.716) H hHp
    _ _ x3_eq x5_eq hQ3 hQ5
  have hq : (1.175 : ℝ) < 284 / 100 * (3 / 2 * (Real.log 2 / Real.log 10)
      + 3.075 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + 4.466 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + (-3.716) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4)
      / (5 / 2 * (Real.log 2 / Real.log 10) + 3.075 * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + 4.466 * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + (-3.716) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 4) := by
    rw [lt_div_iff₀ hQ5]; linarith
  have hlg := Real.logb_lt_logb (by norm_num : (1:ℝ) < 10) (by norm_num) hq
  have := logb_1175
  linarith

/-- **Lusso et al. 2019, SNe + quasars + GRBs, central fit.** For every `Ω ∈ [0, 1]` and every scale
factor obeying `H = H₀ √(Ω(1+z)³ + 1 − Ω)` (with `H₀ > 0`) on the whole interval back to the farther
source, with sources at `1 + z = 2√2` and `1 + z = 4√2`, and every normalisation `H > 0`, the
quartic log-polynomial distance with the printed central coefficients `a₂ = 3.205`, `a₃ = 3.564`,
`a₄ = −2.510` (Table 2) has a residual distance modulus `5 log₁₀(d_L / D_L)` against the exact luminosity
distance `d_L` (`lumDistFlat`) that is larger at the farther source: the residual at
`1 + z = 4√2` exceeds the one at `1 + z = 2√2` by more than 3/10 mag. No normalisation and no
magnitude offset can remove this difference. -/
theorem l19_sqg_central (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1) (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)
    (H : ℝ) (hHp : 0 < H) :
    3 / 10 < 5 * Real.logb 10 (lumDistFlat a t₀ t₅
        / logPolyDL4 3.205 3.564 (-2.510) H (redshift a t₀ t₅))
      - 5 * Real.logb 10 (lumDistFlat a t₀ t₃
        / logPolyDL4 3.205 3.564 (-2.510) H (redshift a t₀ t₃)) := by
  obtain ⟨hL1, hL2⟩ := L_bounds
  obtain ⟨hQ5, hF⟩ := poly_sqg_central _ hL1 hL2
  have hQ3 : 0 < 3 / 2 * (Real.log 2 / Real.log 10) + 3.205 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + 3.564 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + (-2.510) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4 := by linarith
  have hd := delta_ge Ω hΩ₀ hΩ₁ a t₅ t₃ t₀ h₅₃ h₃₀ hpos hdiff hH₀ hH hz₃ hz₅ 3.205 3.564 (-2.510) H hHp
    _ _ x3_eq x5_eq hQ3 hQ5
  have hq : (1.149 : ℝ) < 284 / 100 * (3 / 2 * (Real.log 2 / Real.log 10)
      + 3.205 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + 3.564 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + (-2.510) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4)
      / (5 / 2 * (Real.log 2 / Real.log 10) + 3.205 * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + 3.564 * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + (-2.510) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 4) := by
    rw [lt_div_iff₀ hQ5]; linarith
  have hlg := Real.logb_lt_logb (by norm_num : (1:ℝ) < 10) (by norm_num) hq
  have := logb_1149
  linarith

/-- **Lusso et al. 2019, SNe + quasars, the whole 1σ range.** For every `Ω ∈ [0, 1]` and every scale
factor obeying `H = H₀ √(Ω(1+z)³ + 1 − Ω)` (with `H₀ > 0`) on the whole interval back to the farther
source, with sources at `1 + z = 2√2` and `1 + z = 4√2`, every quartic log-polynomial distance with
`a₂ ≥ 2.906`, `a₃ ≤ 5.479`, `a₄ ≤ −1.794` (the printed Table 2 ends of the 1σ ranges on the side
that brings the quartic's distance ratio closer to the exact one; the region contains the box of all three printed ±1σ ranges), normalisation `H > 0`
and positive at the farther source has a residual distance modulus `5 log₁₀(d_L / D_L)` against
the exact luminosity distance `d_L` (`lumDistFlat`) that is strictly larger at `1 + z = 4√2` than at
`1 + z = 2√2`. -/
theorem l19_sq_box (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1) (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)
    (a₂ a₃ a₄ H : ℝ) (hHp : 0 < H)
    (ha₂ : 2.906 ≤ a₂) (ha₃ : a₃ ≤ 5.479) (ha₄ : a₄ ≤ -1.794)
    (hp₅ : 0 < logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₅)) :
    5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₃))
      < 5 * Real.logb 10 (lumDistFlat a t₀ t₅ / logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₅)) := by
  obtain ⟨hL1, hL2⟩ := L_bounds
  rw [hz₅, lp4_eq a₂ a₃ a₄ H _ _ x5_eq] at hp₅
  have hQ5 := (mul_pos_iff_of_pos_left (div_pos (Real.log_pos (by norm_num)) hHp)).1 hp₅
  have hF := poly_box _ a₂ a₃ a₄ 2.906 5.479 (-1.794) hL1 hL2 ha₂ ha₃ ha₄ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hQ3 : 0 < 3 / 2 * (Real.log 2 / Real.log 10) + a₂ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + a₃ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + a₄ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4 := by linarith
  have hd := delta_ge Ω hΩ₀ hΩ₁ a t₅ t₃ t₀ h₅₃ h₃₀ hpos hdiff hH₀ hH hz₃ hz₅ a₂ a₃ a₄ H hHp
    _ _ x3_eq x5_eq hQ3 hQ5
  have hq : (1 : ℝ) < 284 / 100 * (3 / 2 * (Real.log 2 / Real.log 10)
      + a₂ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + a₃ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + a₄ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4)
      / (5 / 2 * (Real.log 2 / Real.log 10) + a₂ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + a₃ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + a₄ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 4) := by
    rw [lt_div_iff₀ hQ5]; linarith
  have hlg := Real.logb_pos (by norm_num : (1:ℝ) < 10) hq
  linarith

/-- **Lusso et al. 2019, SNe + quasars + GRBs, the whole 1σ range.** For every `Ω ∈ [0, 1]` and
every scale factor obeying `H = H₀ √(Ω(1+z)³ + 1 − Ω)` (with `H₀ > 0`) on the whole interval back to
the farther source, with sources at `1 + z = 2√2` and `1 + z = 4√2`, every quartic log-polynomial
distance with `a₂ ≥ 3.043`, `a₃ ≤ 4.480`, `a₄ ≤ −0.915` (the printed Table 2 ends of the 1σ ranges
on the side that brings the quartic's distance ratio closer to the exact one; the region contains the box of all three printed ±1σ ranges),
normalisation `H > 0` and positive at the farther source has a residual distance modulus
`5 log₁₀(d_L / D_L)` against the exact luminosity distance `d_L` (`lumDistFlat`) that is strictly
larger at `1 + z = 4√2` than at `1 + z = 2√2`. -/
theorem l19_sqg_box (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1) (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)
    (a₂ a₃ a₄ H : ℝ) (hHp : 0 < H)
    (ha₂ : 3.043 ≤ a₂) (ha₃ : a₃ ≤ 4.480) (ha₄ : a₄ ≤ -0.915)
    (hp₅ : 0 < logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₅)) :
    5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₃))
      < 5 * Real.logb 10 (lumDistFlat a t₀ t₅ / logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₅)) := by
  obtain ⟨hL1, hL2⟩ := L_bounds
  rw [hz₅, lp4_eq a₂ a₃ a₄ H _ _ x5_eq] at hp₅
  have hQ5 := (mul_pos_iff_of_pos_left (div_pos (Real.log_pos (by norm_num)) hHp)).1 hp₅
  have hF := poly_box _ a₂ a₃ a₄ 3.043 4.480 (-0.915) hL1 hL2 ha₂ ha₃ ha₄ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hQ3 : 0 < 3 / 2 * (Real.log 2 / Real.log 10) + a₂ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + a₃ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + a₄ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4 := by linarith
  have hd := delta_ge Ω hΩ₀ hΩ₁ a t₅ t₃ t₀ h₅₃ h₃₀ hpos hdiff hH₀ hH hz₃ hz₅ a₂ a₃ a₄ H hHp
    _ _ x3_eq x5_eq hQ3 hQ5
  have hq : (1 : ℝ) < 284 / 100 * (3 / 2 * (Real.log 2 / Real.log 10)
      + a₂ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + a₃ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + a₄ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4)
      / (5 / 2 * (Real.log 2 / Real.log 10) + a₂ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + a₃ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + a₄ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 4) := by
    rw [lt_div_iff₀ hQ5]; linarith
  have hlg := Real.logb_pos (by norm_num : (1:ℝ) < 10) hq
  linarith

end Work.Cosmography.B1L19
