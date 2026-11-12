import Checked.Trust.NonVacuity
import Checked.Cosmography.B1L19
import Checked.Cosmography.B1Separation
import Checked.Cosmography.B1FitRL19
import Checked.Cosmography.B1L19Curved
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Hypothesis necessity, B1 family (trust track T2b, run 2026-11-12T0227Z) — scratch

Generic facts about the flat ΛCDM hypothesis block `hpos, hdiff, hH₀, hH` of the B1 headlines:
* `diff_of_law`: the law `H(s) = H(t₀)·√A(s)` with `A > 0` and `H(t₀) > 0` forces differentiability
  (a junk derivative would make `H(s) = 0`): `hdiff` is REDUNDANT.
* `H0_pos_of_redshift`: the law with `H(t₀) ≤ 0` makes `a` non-increasing, so no earlier time has positive
  redshift: `hH₀` is REDUNDANT whenever a positive redshift is assumed.
-/

open Set Checked.Cosmography

namespace Checked.Trust.NCL

theorem diff_of_law (a : ℝ → ℝ) (t t₀ : ℝ) (A : ℝ → ℝ) (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Icc t t₀, hubble a s = hubble a t₀ * √(A s))
    (hA : ∀ s ∈ Icc t t₀, 0 < A s) : ∀ s ∈ Icc t t₀, DifferentiableAt ℝ a s := by
  intro s hs
  by_contra hd
  have h0 : hubble a s = 0 := by simp [hubble, deriv_zero_of_not_differentiableAt hd]
  have h1 : 0 < hubble a t₀ * √(A s) := mul_pos hH₀ (Real.sqrt_pos.2 (hA s hs))
  have h2 := hH s hs
  linarith

theorem H0_pos_of_redshift (a : ℝ → ℝ) (t t₀ p : ℝ) (A : ℝ → ℝ) (hp : p ∈ Icc t t₀)
    (hpos : ∀ s ∈ Icc t t₀, 0 < a s) (hdiff : ∀ s ∈ Icc t t₀, DifferentiableAt ℝ a s)
    (hH : ∀ s ∈ Icc t t₀, hubble a s = hubble a t₀ * √(A s))
    (hz : 0 < redshift a t₀ p) : 0 < hubble a t₀ := by
  by_contra hle
  have hle : hubble a t₀ ≤ 0 := not_lt.1 hle
  have hderiv : ∀ s ∈ Icc t t₀, deriv a s ≤ 0 := by
    intro s hs
    have h := hH s hs
    have hs0 : hubble a s ≤ 0 := by
      rw [h]; exact mul_nonpos_of_nonpos_of_nonneg hle (Real.sqrt_nonneg _)
    unfold hubble at hs0
    have has := hpos s hs
    by_contra hc
    have := div_pos (not_le.1 hc) has
    linarith
  have hanti : AntitoneOn a (Icc t t₀) :=
    antitoneOn_of_deriv_nonpos (convex_Icc t t₀)
      (fun s hs => (hdiff s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hdiff s (interior_subset hs)).differentiableWithinAt)
      (fun s hs => hderiv s (interior_subset hs))
  have ht₀ : t₀ ∈ Icc t t₀ := ⟨le_trans hp.1 hp.2, le_rfl⟩
  have hle' : a t₀ ≤ a p := hanti hp ht₀ hp.2
  have hap := hpos p hp
  unfold redshift at hz
  have : a t₀ / a p ≤ 1 := (div_le_one hap).2 hle'
  linarith

theorem flat_arg_pos (Ω : ℝ) (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1) (a : ℝ → ℝ) (t₀ s : ℝ)
    (ha₀ : 0 < a t₀) (has : 0 < a s) : 0 < Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω := by
  have hy : 0 < 1 + redshift a t₀ s := by
    unfold redshift; have := div_pos ha₀ has; linarith
  have hy3 : 0 < (1 + redshift a t₀ s) ^ 3 := pow_pos hy 3
  rcases h0.eq_or_lt with h | h
  · subst h; norm_num
  · nlinarith [mul_pos h hy3]

/-- `0 < 4√2 − 1` and `0 < 2√2 − 1`. -/
theorem z5_pos : (0 : ℝ) < 4 * √2 - 1 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

theorem z3_pos : (0 : ℝ) < 2 * √2 - 1 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

section L19
open Checked.Cosmography.B1L19

/-- The flat block on `[t₅, t₀]` with redshift `4√2 − 1` at `t₅` gives `0 < H(t₀)`. -/
theorem flat_H0 (Ω : ℝ) (a : ℝ → ℝ) (t₅ t₀ : ℝ) (h50 : t₅ ≤ t₀)
    (hpos : ∀ s ∈ Icc t₅ t₀, 0 < a s) (hdiff : ∀ s ∈ Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH : ∀ s ∈ Icc t₅ t₀, hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz : 0 < redshift a t₀ t₅) : 0 < hubble a t₀ :=
  H0_pos_of_redshift a t₅ t₀ t₅ (fun s => Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω)
    ⟨le_rfl, h50⟩ hpos hdiff hH hz

theorem flat_diff (Ω : ℝ) (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1) (a : ℝ → ℝ) (t₅ t₀ : ℝ)
    (hpos : ∀ s ∈ Icc t₅ t₀, 0 < a s) (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Icc t₅ t₀, hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω)) :
    ∀ s ∈ Icc t₅ t₀, DifferentiableAt ℝ a s :=
  diff_of_law a t₅ t₀ (fun s => Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω) hH₀ hH
    (fun s hs => flat_arg_pos Ω h0 h1 a t₀ s (hpos t₀ ⟨le_trans hs.1 hs.2, le_rfl⟩) (hpos s hs))

theorem l19_sq_central_r6 : dropped% Checked.Cosmography.B1L19.l19_sq_central 6 := by
  intro Ω h0 h1 a t₅ t₃ t₀ h53 h30 hpos hH₀ hH hz3 hz5 H hHp
  exact l19_sq_central Ω h0 h1 a t₅ t₃ t₀ h53 h30 hpos
    (flat_diff Ω h0 h1 a t₅ t₀ hpos hH₀ hH) hH₀ hH hz3 hz5 H hHp

theorem l19_sq_central_r7 : dropped% Checked.Cosmography.B1L19.l19_sq_central 7 := by
  intro Ω h0 h1 a t₅ t₃ t₀ h53 h30 hpos hdiff hH hz3 hz5 H hHp
  exact l19_sq_central Ω h0 h1 a t₅ t₃ t₀ h53 h30 hpos hdiff
    (flat_H0 Ω a t₅ t₀ (le_trans h53 h30) hpos hdiff hH (hz5 ▸ z5_pos)) hH hz3 hz5 H hHp

theorem l19_sqg_central_r6 : dropped% Checked.Cosmography.B1L19.l19_sqg_central 6 := by
  intro Ω h0 h1 a t₅ t₃ t₀ h53 h30 hpos hH₀ hH hz3 hz5 H hHp
  exact l19_sqg_central Ω h0 h1 a t₅ t₃ t₀ h53 h30 hpos
    (flat_diff Ω h0 h1 a t₅ t₀ hpos hH₀ hH) hH₀ hH hz3 hz5 H hHp

theorem l19_sqg_central_r7 : dropped% Checked.Cosmography.B1L19.l19_sqg_central 7 := by
  intro Ω h0 h1 a t₅ t₃ t₀ h53 h30 hpos hdiff hH hz3 hz5 H hHp
  exact l19_sqg_central Ω h0 h1 a t₅ t₃ t₀ h53 h30 hpos hdiff
    (flat_H0 Ω a t₅ t₀ (le_trans h53 h30) hpos hdiff hH (hz5 ▸ z5_pos)) hH hz3 hz5 H hHp

theorem l19_sq_box_r6 : dropped% Checked.Cosmography.B1L19.l19_sq_box 6 := by
  intro Ω h0 h1 a t₅ t₃ t₀ h53 h30 hpos hH₀ hH hz3 hz5 a₂ a₃ a₄ H hHp ha2 ha3 ha4 hp5
  exact l19_sq_box Ω h0 h1 a t₅ t₃ t₀ h53 h30 hpos
    (flat_diff Ω h0 h1 a t₅ t₀ hpos hH₀ hH) hH₀ hH hz3 hz5 a₂ a₃ a₄ H hHp ha2 ha3 ha4 hp5

theorem l19_sq_box_r7 : dropped% Checked.Cosmography.B1L19.l19_sq_box 7 := by
  intro Ω h0 h1 a t₅ t₃ t₀ h53 h30 hpos hdiff hH hz3 hz5 a₂ a₃ a₄ H hHp ha2 ha3 ha4 hp5
  exact l19_sq_box Ω h0 h1 a t₅ t₃ t₀ h53 h30 hpos hdiff
    (flat_H0 Ω a t₅ t₀ (le_trans h53 h30) hpos hdiff hH (hz5 ▸ z5_pos)) hH hz3 hz5 a₂ a₃ a₄ H hHp
    ha2 ha3 ha4 hp5

theorem l19_sqg_box_r6 : dropped% Checked.Cosmography.B1L19.l19_sqg_box 6 := by
  intro Ω h0 h1 a t₅ t₃ t₀ h53 h30 hpos hH₀ hH hz3 hz5 a₂ a₃ a₄ H hHp ha2 ha3 ha4 hp5
  exact l19_sqg_box Ω h0 h1 a t₅ t₃ t₀ h53 h30 hpos
    (flat_diff Ω h0 h1 a t₅ t₀ hpos hH₀ hH) hH₀ hH hz3 hz5 a₂ a₃ a₄ H hHp ha2 ha3 ha4 hp5

theorem l19_sqg_box_r7 : dropped% Checked.Cosmography.B1L19.l19_sqg_box 7 := by
  intro Ω h0 h1 a t₅ t₃ t₀ h53 h30 hpos hdiff hH hz3 hz5 a₂ a₃ a₄ H hHp ha2 ha3 ha4 hp5
  exact l19_sqg_box Ω h0 h1 a t₅ t₃ t₀ h53 h30 hpos hdiff
    (flat_H0 Ω a t₅ t₀ (le_trans h53 h30) hpos hdiff hH (hz5 ▸ z5_pos)) hH hz3 hz5 a₂ a₃ a₄ H hHp
    ha2 ha3 ha4 hp5

/-! Redshift conditions: with the `z = 2√2 − 1` source moved onto the `z = 4√2 − 1` source (or back), the
two distance-modulus residuals coincide and their difference is `0`, not above the claimed bound.
Model: exact flat ΛCDM at `Ω = 1/5` (`Checked.Cosmography.B1FitWitness.exists_model`). -/

theorem l19_sq_central_h9 : necessity% Checked.Cosmography.B1L19.l19_sq_central 9 := by
  obtain ⟨a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH₀, hH, -, -, hz₅⟩ :=
    Checked.Cosmography.B1FitWitness.exists_model
  exact ⟨1 / 5, by norm_num, by norm_num, a, t₅, t₅, t₀, le_rfl, le_trans h53 (le_trans h31 h10),
    hpos, hdiff, hH₀, hH, hz₅, 1, one_pos, by rw [sub_self]; norm_num⟩

theorem l19_sq_central_h10 : necessity% Checked.Cosmography.B1L19.l19_sq_central 10 := by
  obtain ⟨a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH₀, hH, -, hz₃, -⟩ :=
    Checked.Cosmography.B1FitWitness.exists_model
  have hsub : Icc t₃ t₀ ⊆ Icc t₅ t₀ := Icc_subset_Icc_left h53
  exact ⟨1 / 5, by norm_num, by norm_num, a, t₃, t₃, t₀, le_rfl, le_trans h31 h10,
    fun s hs => hpos s (hsub hs), fun s hs => hdiff s (hsub hs), hH₀, fun s hs => hH s (hsub hs),
    hz₃, 1, one_pos, by rw [sub_self]; norm_num⟩

theorem l19_sqg_central_h9 : necessity% Checked.Cosmography.B1L19.l19_sqg_central 9 := by
  obtain ⟨a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH₀, hH, -, -, hz₅⟩ :=
    Checked.Cosmography.B1FitWitness.exists_model
  exact ⟨1 / 5, by norm_num, by norm_num, a, t₅, t₅, t₀, le_rfl, le_trans h53 (le_trans h31 h10),
    hpos, hdiff, hH₀, hH, hz₅, 1, one_pos, by rw [sub_self]; norm_num⟩

theorem l19_sqg_central_h10 : necessity% Checked.Cosmography.B1L19.l19_sqg_central 10 := by
  obtain ⟨a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH₀, hH, -, hz₃, -⟩ :=
    Checked.Cosmography.B1FitWitness.exists_model
  have hsub : Icc t₃ t₀ ⊆ Icc t₅ t₀ := Icc_subset_Icc_left h53
  exact ⟨1 / 5, by norm_num, by norm_num, a, t₃, t₃, t₀, le_rfl, le_trans h31 h10,
    fun s hs => hpos s (hsub hs), fun s hs => hdiff s (hsub hs), hH₀, fun s hs => hH s (hsub hs),
    hz₃, 1, one_pos, by rw [sub_self]; norm_num⟩

/-- The quartic `x + 3.1x² + 4x³ − 2x⁴` is positive on `(0, 1/2]`. -/
theorem quartic_small (x : ℝ) (hx : 0 < x) (hx2 : x ≤ 1 / 2) :
    0 < x + 31 / 10 * x ^ 2 + 4 * x ^ 3 + -2 * x ^ 4 := by
  have h3 := pow_pos hx 3
  have h2 := pow_pos hx 2
  have h4 : x ^ 4 ≤ x ^ 3 * (1 / 2) := by
    rw [show x ^ 4 = x ^ 3 * x by ring]; exact mul_le_mul_of_nonneg_left hx2 h3.le
  linarith

/-- `logPolyDL4` with `H = 0` is `0` (junk division), so every residual `5 log₁₀(d/0)` is `0`. -/
theorem lp4_H0 (a₂ a₃ a₄ z : ℝ) : logPolyDL4 a₂ a₃ a₄ 0 z = 0 := by simp [logPolyDL4]

theorem l19_sq_central_h11 : necessity% Checked.Cosmography.B1L19.l19_sq_central 11 := by
  obtain ⟨a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH₀, hH, -, hz₃, hz₅⟩ :=
    Checked.Cosmography.B1FitWitness.exists_model
  exact ⟨1 / 5, by norm_num, by norm_num, a, t₅, t₃, t₀, h53, le_trans h31 h10,
    hpos, hdiff, hH₀, hH, hz₃, hz₅, 0, by norm_num [lp4_H0]⟩

theorem l19_sqg_central_h11 : necessity% Checked.Cosmography.B1L19.l19_sqg_central 11 := by
  obtain ⟨a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH₀, hH, -, hz₃, hz₅⟩ :=
    Checked.Cosmography.B1FitWitness.exists_model
  exact ⟨1 / 5, by norm_num, by norm_num, a, t₅, t₃, t₀, h53, le_trans h31 h10,
    hpos, hdiff, hH₀, hH, hz₃, hz₅, 0, by norm_num [lp4_H0]⟩

theorem l19_sq_box_h9 : necessity% Checked.Cosmography.B1L19.l19_sq_box 9 := by
  obtain ⟨a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH₀, hH, -, -, hz₅⟩ :=
    Checked.Cosmography.B1FitWitness.exists_model
  refine ⟨1 / 5, by norm_num, by norm_num, a, t₅, t₅, t₀, le_rfl, le_trans h53 (le_trans h31 h10),
    hpos, hdiff, hH₀, hH, hz₅, 31 / 10, 4, -2, 1, one_pos, by norm_num, by norm_num, by norm_num,
    ?_, lt_irrefl _⟩
  rw [hz₅]
  exact quartic_pos5 _ _ _ 1 one_pos (31 / 10) 4 (-2) le_rfl le_rfl le_rfl (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem l19_sq_box_h10 : necessity% Checked.Cosmography.B1L19.l19_sq_box 10 := by
  obtain ⟨a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH₀, hH, -, hz₃, -⟩ :=
    Checked.Cosmography.B1FitWitness.exists_model
  have hsub : Icc t₃ t₀ ⊆ Icc t₅ t₀ := Icc_subset_Icc_left h53
  refine ⟨1 / 5, by norm_num, by norm_num, a, t₃, t₃, t₀, le_rfl, le_trans h31 h10,
    fun s hs => hpos s (hsub hs), fun s hs => hdiff s (hsub hs), hH₀, fun s hs => hH s (hsub hs),
    hz₃, 31 / 10, 4, -2, 1, one_pos, by norm_num, by norm_num, by norm_num, ?_, lt_irrefl _⟩
  rw [hz₃, lp4_eq _ _ _ _ _ _ x3_eq]
  obtain ⟨hL1, hL2⟩ := L_bounds
  have hl0 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  exact mul_pos (div_pos hl0 one_pos) (quartic_small _ (by linarith) (by linarith))

theorem l19_sqg_box_h9 : necessity% Checked.Cosmography.B1L19.l19_sqg_box 9 := by
  obtain ⟨a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH₀, hH, -, -, hz₅⟩ :=
    Checked.Cosmography.B1FitWitness.exists_model
  refine ⟨1 / 5, by norm_num, by norm_num, a, t₅, t₅, t₀, le_rfl, le_trans h53 (le_trans h31 h10),
    hpos, hdiff, hH₀, hH, hz₅, 31 / 10, 4, -2, 1, one_pos, by norm_num, by norm_num, by norm_num,
    ?_, lt_irrefl _⟩
  rw [hz₅]
  exact quartic_pos5 _ _ _ 1 one_pos (31 / 10) 4 (-2) le_rfl le_rfl le_rfl (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem l19_sqg_box_h10 : necessity% Checked.Cosmography.B1L19.l19_sqg_box 10 := by
  obtain ⟨a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH₀, hH, -, hz₃, -⟩ :=
    Checked.Cosmography.B1FitWitness.exists_model
  have hsub : Icc t₃ t₀ ⊆ Icc t₅ t₀ := Icc_subset_Icc_left h53
  refine ⟨1 / 5, by norm_num, by norm_num, a, t₃, t₃, t₀, le_rfl, le_trans h31 h10,
    fun s hs => hpos s (hsub hs), fun s hs => hdiff s (hsub hs), hH₀, fun s hs => hH s (hsub hs),
    hz₃, 31 / 10, 4, -2, 1, one_pos, by norm_num, by norm_num, by norm_num, ?_, lt_irrefl _⟩
  rw [hz₃, lp4_eq _ _ _ _ _ _ x3_eq]
  obtain ⟨hL1, hL2⟩ := L_bounds
  have hl0 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  exact mul_pos (div_pos hl0 one_pos) (quartic_small _ (by linarith) (by linarith))

end L19

section B1
open Checked.Cosmography.B1 Checked.Cosmography.BambaY

theorem lumDistFlat_flatLCDM_r5 : dropped% Checked.Cosmography.B1.lumDistFlat_flatLCDM 5 := by
  intro Ω h0 h1 a t t₀ htt hpos hH₀ hH
  exact lumDistFlat_flatLCDM Ω h0 h1 a t t₀ htt hpos (flat_diff Ω h0 h1 a t t₀ hpos hH₀ hH) hH₀ hH

/-- Without `0 < H(t₀)`: the static model `a ≡ 1` meets the law with `H ≡ 0`; its distance from
`t = −1` is `1`, while the formula divides by `H(t₀) = 0` and gives `0`. -/
theorem lumDistFlat_flatLCDM_h6 : necessity% Checked.Cosmography.B1.lumDistFlat_flatLCDM 6 := by
  refine ⟨0, le_rfl, zero_le_one, fun _ => 1, -1, 0, by norm_num, fun _ _ => one_pos,
    fun _ _ => differentiableAt_const _, fun _ _ => by simp [hubble], ?_⟩
  simp [lumDistFlat, comoving, redshift, hubble]

theorem cubic_misses_z3_r5 : dropped% Checked.Cosmography.B1.cubic_misses_z3 5 := by
  intro Ω h1 h2 a t t₀ htt hpos hH₀ hH hz
  exact cubic_misses_z3 Ω h1 h2 a t t₀ htt hpos
    (flat_diff Ω (by linarith) (by linarith) a t t₀ hpos hH₀ hH) hH₀ hH hz

theorem cubic_misses_z3_r6 : dropped% Checked.Cosmography.B1.cubic_misses_z3 6 := by
  intro Ω h1 h2 a t t₀ htt hpos hdiff hH hz
  exact cubic_misses_z3 Ω h1 h2 a t t₀ htt hpos hdiff
    (flat_H0 Ω a t t₀ htt hpos hdiff hH (by rw [hz]; norm_num)) hH hz

theorem cubic_misses_z7_r5 : dropped% Checked.Cosmography.B1.cubic_misses_z7 5 := by
  intro Ω h1 h2 a t t₀ htt hpos hH₀ hH hz
  exact cubic_misses_z7 Ω h1 h2 a t t₀ htt hpos
    (flat_diff Ω (by linarith) (by linarith) a t t₀ hpos hH₀ hH) hH₀ hH hz

theorem cubic_misses_z7_r6 : dropped% Checked.Cosmography.B1.cubic_misses_z7 6 := by
  intro Ω h1 h2 a t t₀ htt hpos hdiff hH hz
  exact cubic_misses_z7 Ω h1 h2 a t t₀ htt hpos hdiff
    (flat_H0 Ω a t t₀ htt hpos hdiff hH (by rw [hz]; norm_num)) hH hz

/-- The redshift at the observation time is `0`, where the cubic distance is `0`. -/
theorem lp3_now (a : ℝ → ℝ) (t₀ a₂ a₃ H : ℝ) (ha : a t₀ ≠ 0) :
    logPolyDL3 a₂ a₃ H (redshift a t₀ t₀) = 0 := by
  simp [logPolyDL3, redshift, div_self ha]

theorem cubic_misses_z3_h8 : necessity% Checked.Cosmography.B1.cubic_misses_z3 8 := by
  obtain ⟨a, t₇, t₃, t₀, h73, h30, hpos, hdiff, hH₀, hH, -, -⟩ := exists_flatLCDM_on
  have hsub : Icc t₀ t₀ ⊆ Icc t₇ t₀ := Icc_subset_Icc_left (le_trans h73 h30)
  have ha : a t₀ ≠ 0 := (hpos t₀ ⟨le_trans h73 h30, le_rfl⟩).ne'
  exact ⟨1 / 5, by norm_num, by norm_num, a, t₀, t₀, le_rfl, fun s hs => hpos s (hsub hs),
    fun s hs => hdiff s (hsub hs), hH₀, fun s hs => hH s (hsub hs),
    fun h => (lt_irrefl (0 : ℝ)) (by simpa [lp3_now a t₀ _ _ _ ha] using h.1)⟩

theorem cubic_misses_z7_h8 : necessity% Checked.Cosmography.B1.cubic_misses_z7 8 := by
  obtain ⟨a, t₇, t₃, t₀, h73, h30, hpos, hdiff, hH₀, hH, -, -⟩ := exists_flatLCDM_on
  have hsub : Icc t₀ t₀ ⊆ Icc t₇ t₀ := Icc_subset_Icc_left (le_trans h73 h30)
  have ha : a t₀ ≠ 0 := (hpos t₀ ⟨le_trans h73 h30, le_rfl⟩).ne'
  exact ⟨1 / 5, by norm_num, by norm_num, a, t₀, t₀, le_rfl, fun s hs => hpos s (hsub hs),
    fun s hs => hdiff s (hsub hs), hH₀, fun s hs => hH s (hsub hs),
    fun h => (lt_irrefl (0 : ℝ)) (by simpa [lp3_now a t₀ _ _ _ ha] using h.1)⟩

theorem cubic_shape_miss_r6 : dropped% Checked.Cosmography.B1.cubic_shape_miss 6 := by
  intro Ω h1 h2 a t₇ t₃ t₀ h73 h30 hpos hH₀ hH hz3 hz7
  exact cubic_shape_miss Ω h1 h2 a t₇ t₃ t₀ h73 h30 hpos
    (flat_diff Ω (by linarith) (by linarith) a t₇ t₀ hpos hH₀ hH) hH₀ hH hz3 hz7

theorem cubic_shape_miss_r7 : dropped% Checked.Cosmography.B1.cubic_shape_miss 7 := by
  intro Ω h1 h2 a t₇ t₃ t₀ h73 h30 hpos hdiff hH hz3 hz7
  exact cubic_shape_miss Ω h1 h2 a t₇ t₃ t₀ h73 h30 hpos hdiff
    (flat_H0 Ω a t₇ t₀ (le_trans h73 h30) hpos hdiff hH (by rw [hz7]; norm_num)) hH hz3 hz7

theorem cubic_shape_miss_h9 : necessity% Checked.Cosmography.B1.cubic_shape_miss 9 := by
  obtain ⟨a, t₇, t₃, t₀, h73, h30, hpos, hdiff, hH₀, hH, -, hz7⟩ := exists_flatLCDM_on
  exact ⟨1 / 5, by norm_num, by norm_num, a, t₇, t₇, t₀, le_rfl, le_trans h73 h30, hpos, hdiff,
    hH₀, hH, hz7, by rw [sub_self]; norm_num⟩

theorem cubic_shape_miss_h10 : necessity% Checked.Cosmography.B1.cubic_shape_miss 10 := by
  obtain ⟨a, t₇, t₃, t₀, h73, h30, hpos, hdiff, hH₀, hH, hz3, -⟩ := exists_flatLCDM_on
  have hsub : Icc t₃ t₀ ⊆ Icc t₇ t₀ := Icc_subset_Icc_left h73
  exact ⟨1 / 5, by norm_num, by norm_num, a, t₃, t₃, t₀, le_rfl, h30,
    fun s hs => hpos s (hsub hs), fun s hs => hdiff s (hsub hs), hH₀, fun s hs => hH s (hsub hs),
    hz3, by rw [sub_self]; norm_num⟩

end B1

section B1Sep
open Checked.Cosmography.B1 Checked.Cosmography.B1Sep Checked.Cosmography.BambaY

theorem cubic_separation_r6 : dropped% Checked.Cosmography.B1Sep.cubic_separation 6 := by
  intro Ω h1 h2 a t₇ t₃ t₀ h73 h30 hpos hH₀ hH hz3 hz7 a₂ a₃ H c hHp hp3 hp7 hm3 hm7
  exact cubic_separation Ω h1 h2 a t₇ t₃ t₀ h73 h30 hpos
    (flat_diff Ω (by linarith) (by linarith) a t₇ t₀ hpos hH₀ hH) hH₀ hH hz3 hz7 a₂ a₃ H c hHp
    hp3 hp7 hm3 hm7

theorem cubic_separation_r7 : dropped% Checked.Cosmography.B1Sep.cubic_separation 7 := by
  intro Ω h1 h2 a t₇ t₃ t₀ h73 h30 hpos hdiff hH hz3 hz7 a₂ a₃ H c hHp hp3 hp7 hm3 hm7
  exact cubic_separation Ω h1 h2 a t₇ t₃ t₀ h73 h30 hpos hdiff
    (flat_H0 Ω a t₇ t₀ (le_trans h73 h30) hpos hdiff hH (by rw [hz7]; norm_num)) hH hz3 hz7
    a₂ a₃ H c hHp hp3 hp7 hm3 hm7

theorem cubic_direction_r6 : dropped% Checked.Cosmography.B1Sep.cubic_direction 6 := by
  intro Ω h1 h2 a t₇ t₃ t₀ h73 h30 hpos hH₀ hH hz3 hz7 a₂ a₃ H c hHp hp3 hp7 hm3 hm7
  exact cubic_direction Ω h1 h2 a t₇ t₃ t₀ h73 h30 hpos
    (flat_diff Ω (by linarith) (by linarith) a t₇ t₀ hpos hH₀ hH) hH₀ hH hz3 hz7 a₂ a₃ H c hHp
    hp3 hp7 hm3 hm7

theorem cubic_direction_r7 : dropped% Checked.Cosmography.B1Sep.cubic_direction 7 := by
  intro Ω h1 h2 a t₇ t₃ t₀ h73 h30 hpos hdiff hH hz3 hz7 a₂ a₃ H c hHp hp3 hp7 hm3 hm7
  exact cubic_direction Ω h1 h2 a t₇ t₃ t₀ h73 h30 hpos hdiff
    (flat_H0 Ω a t₇ t₀ (le_trans h73 h30) hpos hdiff hH (by rw [hz7]; norm_num)) hH hz3 hz7
    a₂ a₃ H c hHp hp3 hp7 hm3 hm7

/-! Redshift conditions of the separation pair: with both sources at the same redshift, the ΛCDM
coefficients themselves (`lusA2`, `lusA3` at `Ω = 1/5`, `H = H(t₀)`) match both residuals to one
constant, so the claimed separation and direction fail (both sides are `0`). -/

theorem cubic_separation_h9 : necessity% Checked.Cosmography.B1Sep.cubic_separation 9 := by
  obtain ⟨a, t₇, t₃, t₀, h73, h30, hpos, hdiff, hH₀, hH, -, hz7⟩ := exists_flatLCDM_on
  have hp := (cubic_misses_z7 (1 / 5) (by norm_num) (by norm_num) a t₇ t₀ (le_trans h73 h30)
    hpos hdiff hH₀ hH hz7).1
  exact ⟨1 / 5, by norm_num, by norm_num, a, t₇, t₇, t₀, le_rfl, le_trans h73 h30, hpos, hdiff,
    hH₀, hH, hz7, lusA2 (1 / 5), lusA3 (1 / 5), hubble a t₀, _, hH₀, hp, hp,
    by rw [sub_self, abs_zero]; norm_num, by rw [sub_self, abs_zero]; norm_num,
    by rw [sub_self, sub_self]; norm_num⟩

theorem cubic_separation_h10 : necessity% Checked.Cosmography.B1Sep.cubic_separation 10 := by
  obtain ⟨a, t₇, t₃, t₀, h73, h30, hpos, hdiff, hH₀, hH, hz3, -⟩ := exists_flatLCDM_on
  have hsub : Icc t₃ t₀ ⊆ Icc t₇ t₀ := Icc_subset_Icc_left h73
  have hp := (cubic_misses_z3 (1 / 5) (by norm_num) (by norm_num) a t₃ t₀ h30
    (fun s hs => hpos s (hsub hs)) (fun s hs => hdiff s (hsub hs)) hH₀
    (fun s hs => hH s (hsub hs)) hz3).1
  exact ⟨1 / 5, by norm_num, by norm_num, a, t₃, t₃, t₀, le_rfl, h30,
    fun s hs => hpos s (hsub hs), fun s hs => hdiff s (hsub hs), hH₀, fun s hs => hH s (hsub hs),
    hz3, lusA2 (1 / 5), lusA3 (1 / 5), hubble a t₀, _, hH₀, hp, hp,
    by rw [sub_self, abs_zero]; norm_num, by rw [sub_self, abs_zero]; norm_num,
    by rw [sub_self, sub_self]; norm_num⟩

theorem cubic_direction_h9 : necessity% Checked.Cosmography.B1Sep.cubic_direction 9 := by
  obtain ⟨a, t₇, t₃, t₀, h73, h30, hpos, hdiff, hH₀, hH, -, hz7⟩ := exists_flatLCDM_on
  have hp := (cubic_misses_z7 (1 / 5) (by norm_num) (by norm_num) a t₇ t₀ (le_trans h73 h30)
    hpos hdiff hH₀ hH hz7).1
  exact ⟨1 / 5, by norm_num, by norm_num, a, t₇, t₇, t₀, le_rfl, le_trans h73 h30, hpos, hdiff,
    hH₀, hH, hz7, lusA2 (1 / 5), lusA3 (1 / 5), hubble a t₀, _, hH₀, hp, hp,
    by rw [sub_self, abs_zero]; norm_num, by rw [sub_self, abs_zero]; norm_num,
    by rw [sub_self, sub_self]; norm_num⟩

theorem cubic_direction_h10 : necessity% Checked.Cosmography.B1Sep.cubic_direction 10 := by
  obtain ⟨a, t₇, t₃, t₀, h73, h30, hpos, hdiff, hH₀, hH, hz3, -⟩ := exists_flatLCDM_on
  have hsub : Icc t₃ t₀ ⊆ Icc t₇ t₀ := Icc_subset_Icc_left h73
  have hp := (cubic_misses_z3 (1 / 5) (by norm_num) (by norm_num) a t₃ t₀ h30
    (fun s hs => hpos s (hsub hs)) (fun s hs => hdiff s (hsub hs)) hH₀
    (fun s hs => hH s (hsub hs)) hz3).1
  exact ⟨1 / 5, by norm_num, by norm_num, a, t₃, t₃, t₀, le_rfl, h30,
    fun s hs => hpos s (hsub hs), fun s hs => hdiff s (hsub hs), hH₀, fun s hs => hH s (hsub hs),
    hz3, lusA2 (1 / 5), lusA3 (1 / 5), hubble a t₀, _, hH₀, hp, hp,
    by rw [sub_self, abs_zero]; norm_num, by rw [sub_self, abs_zero]; norm_num,
    by rw [sub_self, sub_self]; norm_num⟩

end B1Sep

section B1Fit
open Checked.Cosmography.B1 Checked.Cosmography.B1Fit Checked.Cosmography.B1FitRL19

theorem fit_direction_r7 : dropped% Checked.Cosmography.B1Fit.fit_direction 7 := by
  intro Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hH₀ hH hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5
    hm1 hm3 hm5
  exact fit_direction Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos
    (flat_diff Ω h0 h1 a t₅ t₀ hpos hH₀ hH) hH₀ hH hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5
    hm1 hm3 hm5

theorem fit_direction_r8 : dropped% Checked.Cosmography.B1Fit.fit_direction 8 := by
  intro Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5
    hm1 hm3 hm5
  exact fit_direction Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff
    (flat_H0 Ω a t₅ t₀ (le_trans h53 (le_trans h31 h10)) hpos hdiff hH (hz5 ▸ z5_pos))
    hH hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5 hm1 hm3 hm5

theorem rl19_box_unmatched_r7 : dropped% Checked.Cosmography.B1FitRL19.rl19_box_unmatched 7 := by
  intro Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hH₀ hH hz1 hz3 hz5 a₂ a₃ H c h2l h2u h3l h3u hHp
    hp1 hp3 hp5
  exact rl19_box_unmatched Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos
    (flat_diff Ω h0 h1 a t₅ t₀ hpos hH₀ hH) hH₀ hH hz1 hz3 hz5 a₂ a₃ H c h2l h2u h3l h3u hHp
    hp1 hp3 hp5

theorem rl19_box_unmatched_r8 : dropped% Checked.Cosmography.B1FitRL19.rl19_box_unmatched 8 := by
  intro Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff hH hz1 hz3 hz5 a₂ a₃ H c h2l h2u h3l h3u hHp
    hp1 hp3 hp5
  exact rl19_box_unmatched Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hpos hdiff
    (flat_H0 Ω a t₅ t₀ (le_trans h53 (le_trans h31 h10)) hpos hdiff hH (hz5 ▸ z5_pos))
    hH hz1 hz3 hz5 a₂ a₃ H c h2l h2u h3l h3u hHp hp1 hp3 hp5

end B1Fit

section L19Box
open Checked.Cosmography.B1 Checked.Cosmography.B1L19 Checked.Cosmography.B1Fit
  Checked.Cosmography.BambaY

/-! Coefficient conditions of the two box theorems. In the exact flat ΛCDM model at `Ω = 1/5` the two
distances satisfy `d₅ ≤ 4 d₃` (`model_ratio`: the integrand `gL (1/5)` is at most `9/2` and at least `2`
on `[w₃, 1]`). A quartic with `|P(x₅)| ≥ 4 |P(x₃)|` then makes the `z = 4√2 − 1` residual no larger than
the `z = 2√2 − 1` one (`no_rise`), so each box condition, the positivity at `x₅` and `0 < H` are needed:
each witness keeps every other condition and violates only its own. -/

theorem gL5_le (v : ℝ) : gL (1 / 5) v ≤ 9 / 2 := by
  unfold gL
  have h1 : (4 / 9 : ℝ) ≤ √(1 / 5 + (1 - 1 / 5) * v ^ 6) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [pow_two_nonneg (v ^ 3), show v ^ 6 = (v ^ 3) ^ 2 by ring]
  rw [div_le_iff₀ (by linarith)]; linarith

theorem gL5_ge (v : ℝ) (h0 : 0 ≤ v) (h1 : v ≤ 1) : 2 ≤ gL (1 / 5) v := by
  unfold gL
  have hv6 : v ^ 6 ≤ 1 := pow_le_one₀ h0 h1
  have hs : √(1 / 5 + (1 - 1 / 5) * v ^ 6) ≤ 1 := by
    rw [Real.sqrt_le_one]; nlinarith
  have hp : 0 < √(1 / 5 + (1 - 1 / 5) * v ^ 6) := Real.sqrt_pos.2 (by positivity)
  rw [le_div_iff₀ hp]; linarith

theorem model_ratio (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Icc t₅ t₀, 0 < a s) (hdiff : ∀ s ∈ Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(1 / 5 * (1 + redshift a t₀ s) ^ 3 + 1 - 1 / 5))
    (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1) (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1) :
    0 < lumDistFlat a t₀ t₃ ∧ lumDistFlat a t₀ t₅ ≤ 4 * lumDistFlat a t₀ t₃ := by
  have h₅₀ : t₅ ≤ t₀ := le_trans h₅₃ h₃₀
  have hsub3 : Icc t₃ t₀ ⊆ Icc t₅ t₀ := Icc_subset_Icc_left h₅₃
  have hbr3 := lumDistFlat_flatLCDM (1 / 5) (by norm_num) (by norm_num) a t₃ t₀ h₃₀
    (fun s hs => hpos s (hsub3 hs)) (fun s hs => hdiff s (hsub3 hs)) hH₀ (fun s hs => hH s (hsub3 hs))
  have hbr5 := lumDistFlat_flatLCDM (1 / 5) (by norm_num) (by norm_num) a t₅ t₀ h₅₀ hpos hdiff hH₀ hH
  have ha₀ : 0 < a t₀ := hpos t₀ ⟨h₅₀, le_rfl⟩
  have ha3 : 0 < a t₃ := hpos t₃ ⟨h₅₃, h₃₀⟩
  have ha5 : 0 < a t₅ := hpos t₅ ⟨le_rfl, h₅₀⟩
  have es3 : (1:ℝ) + (2 * √2 - 1) = 2 * √2 := by ring
  have es5 : (1:ℝ) + (4 * √2 - 1) = 4 * √2 := by ring
  rw [ratio_of_z a t₃ t₀ _ ha3 ha₀ hz₃, es3, hz₃, es3] at hbr3
  rw [ratio_of_z a t₅ t₀ _ ha5 ha₀ hz₅, es5, hz₅, es5] at hbr5
  change lumDistFlat a t₀ t₃ = 2 * √2 / hubble a t₀ * ∫ v in √(1 / (2 * √2))..1, gL (1 / 5) v at hbr3
  change lumDistFlat a t₀ t₅ = 4 * √2 / hubble a t₀ * ∫ v in √(1 / (4 * √2))..1, gL (1 / 5) v at hbr5
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  obtain ⟨w3u, w3l⟩ := wb (2 * √2) (148651 / 250000) (594603 / 1000000) (by positivity)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  obtain ⟨w5u, w5l⟩ := wb (4 * √2) (420449 / 1000000) (13139 / 31250) (by positivity)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  set w3 := √(1 / (2 * √2)) with hw3
  set w5 := √(1 / (4 * √2)) with hw5
  have hint : ∀ x y : ℝ, w5 ≤ x → w5 ≤ y →
      IntervalIntegrable (gL (1 / 5)) MeasureTheory.volume x y := by
    intro x y hx hy
    apply (gL_cont (1 / 5) (by norm_num) (by norm_num)).mono _ |>.intervalIntegrable
    intro z hz; rcases mem_uIcc.1 hz with h | h
    · exact lt_of_lt_of_le (by linarith) (le_trans hx h.1)
    · exact lt_of_lt_of_le (by linarith) (le_trans hy h.1)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint w5 w3 le_rfl (by linarith))
    (hint w3 1 (by linarith) (by linarith))
  have hI : ∫ v in w5..w3, gL (1 / 5) v ≤ ∫ v in w5..w3, (9 / 2 : ℝ) :=
    intervalIntegral.integral_mono_on (by linarith) (hint w5 w3 le_rfl (by linarith))
      intervalIntegrable_const (fun v _ => gL5_le v)
  have hJ : ∫ v in w3..1, (2 : ℝ) ≤ ∫ v in w3..1, gL (1 / 5) v :=
    intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      (hint w3 1 (by linarith) (by linarith))
      (fun v hv => gL5_ge v (by linarith [hv.1]) hv.2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hI hJ
  set J3 := ∫ v in w3..1, gL (1 / 5) v
  set I := ∫ v in w5..w3, gL (1 / 5) v
  have hJ3 : 0 < J3 := by nlinarith
  have hc : 0 < 2 * √2 / hubble a t₀ := by positivity
  rw [hbr3, hbr5, ← hsplit]
  refine ⟨mul_pos hc hJ3, ?_⟩
  have hIJ : I ≤ J3 := by nlinarith
  have e : 4 * √2 / hubble a t₀ = 2 * (2 * √2 / hubble a t₀) := by ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hIJ hc.le]

/-- With `d₅ ≤ 4 d₃` and `|P₅| ≥ 4 |P₃|` the residual at the far source is not larger. -/
theorem no_rise (d₃ d₅ P₃ P₅ : ℝ) (hd₃ : 0 < d₃) (hd₅ : 0 < d₅) (hd : d₅ ≤ 4 * d₃)
    (hP₃ : P₃ ≠ 0) (hP : 4 * |P₃| ≤ |P₅|) :
    ¬ (5 * Real.logb 10 (d₃ / P₃) < 5 * Real.logb 10 (d₅ / P₅)) := by
  have hA₃ : 0 < |P₃| := abs_pos.2 hP₃
  have hA₅ : 0 < |P₅| := by linarith
  rw [← Real.logb_abs 10 (d₃ / P₃), ← Real.logb_abs 10 (d₅ / P₅), abs_div, abs_div, abs_of_pos hd₃,
    abs_of_pos hd₅]
  apply not_lt.2
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.logb_le_logb_of_le (by norm_num) (div_pos hd₅ hA₅)
  rw [div_le_div_iff₀ hA₅ hA₃]
  nlinarith [mul_le_mul_of_nonneg_left hP hd₃.le, mul_le_mul_of_nonneg_right hd hA₃.le]

/-- `|logPolyDL4 … z| = (ln 10/|H|) |Q(x)|`, so `4|P₃| ≤ |P₅|` reduces to the quartics. -/
theorem lp4_abs_ratio (a₂ a₃ a₄ H x₃ x₅ z₃ z₅ : ℝ)
    (h₃ : Real.logb 10 (1 + z₃) = x₃) (h₅ : Real.logb 10 (1 + z₅) = x₅)
    (hQ : 4 * |x₃ + a₂ * x₃ ^ 2 + a₃ * x₃ ^ 3 + a₄ * x₃ ^ 4|
      ≤ |x₅ + a₂ * x₅ ^ 2 + a₃ * x₅ ^ 3 + a₄ * x₅ ^ 4|) :
    4 * |logPolyDL4 a₂ a₃ a₄ H z₃| ≤ |logPolyDL4 a₂ a₃ a₄ H z₅| := by
  rw [lp4_eq _ _ _ _ _ _ h₃, lp4_eq _ _ _ _ _ _ h₅, abs_mul, abs_mul]
  have : 0 ≤ |Real.log 10 / H| := abs_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hQ this]

theorem L_pows : (30101 / 100000 : ℝ) ≤ Real.log 2 / Real.log 10 ∧
    Real.log 2 / Real.log 10 ≤ 30105 / 100000 ∧
    (30101 / 100000 : ℝ) ^ 2 ≤ (Real.log 2 / Real.log 10) ^ 2 ∧
    (Real.log 2 / Real.log 10) ^ 2 ≤ (30105 / 100000) ^ 2 ∧
    (30101 / 100000 : ℝ) ^ 3 ≤ (Real.log 2 / Real.log 10) ^ 3 ∧
    (Real.log 2 / Real.log 10) ^ 3 ≤ (30105 / 100000) ^ 3 ∧
    (30101 / 100000 : ℝ) ^ 4 ≤ (Real.log 2 / Real.log 10) ^ 4 ∧
    (Real.log 2 / Real.log 10) ^ 4 ≤ (30105 / 100000) ^ 4 := by
  obtain ⟨h1, h2⟩ := L_bounds
  have h0 : (0 : ℝ) ≤ 30101 / 100000 := by norm_num
  refine ⟨h1, h2, pow_le_pow_left₀ h0 h1 2, pow_le_pow_left₀ (le_trans h0 h1) h2 2,
    pow_le_pow_left₀ h0 h1 3, pow_le_pow_left₀ (le_trans h0 h1) h2 3,
    pow_le_pow_left₀ h0 h1 4, pow_le_pow_left₀ (le_trans h0 h1) h2 4⟩

/-- In the model of `model_ratio`, any quartic with `|Q(x₅)| ≥ 4|Q(x₃)| > 0` and `H ≠ 0` makes the box
theorems' conclusion false. -/
theorem box_fails (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Icc t₅ t₀, 0 < a s) (hdiff : ∀ s ∈ Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(1 / 5 * (1 + redshift a t₀ s) ^ 3 + 1 - 1 / 5))
    (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1) (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)
    (a₂ a₃ a₄ H : ℝ) (hH0 : H ≠ 0)
    (hQ₃ : 3 / 2 * (Real.log 2 / Real.log 10) + a₂ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + a₃ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + a₄ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4 ≠ 0)
    (hQ : 4 * |3 / 2 * (Real.log 2 / Real.log 10) + a₂ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + a₃ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + a₄ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4|
      ≤ |5 / 2 * (Real.log 2 / Real.log 10) + a₂ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + a₃ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + a₄ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 4|) :
    ¬ (5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₃))
      < 5 * Real.logb 10 (lumDistFlat a t₀ t₅ / logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₅))) := by
  obtain ⟨hd₃, hd⟩ := model_ratio a t₅ t₃ t₀ h₅₃ h₃₀ hpos hdiff hH₀ hH hz₃ hz₅
  have hd₅ : 0 < lumDistFlat a t₀ t₅ := by
    have h₅₀ : t₅ ≤ t₀ := le_trans h₅₃ h₃₀
    have hbr5 := lumDistFlat_flatLCDM (1 / 5) (by norm_num) (by norm_num) a t₅ t₀ h₅₀ hpos hdiff
      hH₀ hH
    have ha₀ : 0 < a t₀ := hpos t₀ ⟨h₅₀, le_rfl⟩
    have ha5 : 0 < a t₅ := hpos t₅ ⟨le_rfl, h₅₀⟩
    rw [ratio_of_z a t₅ t₀ _ ha5 ha₀ hz₅, hz₅] at hbr5
    obtain ⟨hq2l, -⟩ := sqrt2_bounds
    obtain ⟨hw0, hw1⟩ := w_lt_one (1 + (4 * √2 - 1)) (by linarith)
    rw [hbr5]
    exact mul_pos (div_pos (by linarith) hH₀) (Jpos (1 / 5) _ (by norm_num) (by norm_num) hw0 hw1)
  rw [hz₃, hz₅]
  apply no_rise _ _ _ _ hd₃ hd₅ hd
  · rw [lp4_eq _ _ _ _ _ _ x3_eq]
    exact mul_ne_zero (div_ne_zero (Real.log_pos (by norm_num)).ne' hH0) hQ₃
  · exact lp4_abs_ratio _ _ _ _ _ _ _ _ x3_eq x5_eq hQ

theorem l19_sq_box_h11 : necessity% Checked.Cosmography.B1L19.l19_sq_box 11 := by
  obtain ⟨a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH₀, hH, -, hz₃, hz₅⟩ :=
    Checked.Cosmography.B1FitWitness.exists_model
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := L_pows
  refine ⟨1 / 5, by norm_num, by norm_num, a, t₅, t₃, t₀, h53, le_trans h31 h10, hpos, hdiff, hH₀,
    hH, hz₃, hz₅, 2.906, 5.479, -30, -1, by norm_num, by norm_num, by norm_num, ?_,
    box_fails a t₅ t₃ t₀ h53 (le_trans h31 h10) hpos hdiff hH₀ hH hz₃ hz₅ _ _ _ _ (by norm_num)
      ?_ ?_⟩
  · rw [hz₅, lp4_eq _ _ _ _ _ _ x5_eq]
    apply mul_pos_of_neg_of_neg (div_neg_of_pos_of_neg (Real.log_pos (by norm_num)) (by norm_num))
    nlinarith
  · nlinarith
  · rw [abs_of_pos (by nlinarith), abs_of_neg (by nlinarith)]; nlinarith

theorem l19_sq_box_h12 : necessity% Checked.Cosmography.B1L19.l19_sq_box 12 := by
  obtain ⟨a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH₀, hH, -, hz₃, hz₅⟩ :=
    Checked.Cosmography.B1FitWitness.exists_model
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := L_pows
  refine ⟨1 / 5, by norm_num, by norm_num, a, t₅, t₃, t₀, h53, le_trans h31 h10, hpos, hdiff, hH₀,
    hH, hz₃, hz₅, -21 / 5, 5.479, -1.794, 1, one_pos, by norm_num, by norm_num, ?_,
    box_fails a t₅ t₃ t₀ h53 (le_trans h31 h10) hpos hdiff hH₀ hH hz₃ hz₅ _ _ _ _ (by norm_num)
      ?_ ?_⟩
  · rw [hz₅, lp4_eq _ _ _ _ _ _ x5_eq]
    exact mul_pos (div_pos (Real.log_pos (by norm_num)) one_pos) (by nlinarith)
  · nlinarith
  · rw [abs_of_pos (by nlinarith), abs_of_pos (by nlinarith)]; nlinarith

theorem l19_sq_box_h13 : necessity% Checked.Cosmography.B1L19.l19_sq_box 13 := by
  obtain ⟨a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH₀, hH, -, hz₃, hz₅⟩ :=
    Checked.Cosmography.B1FitWitness.exists_model
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := L_pows
  refine ⟨1 / 5, by norm_num, by norm_num, a, t₅, t₃, t₀, h53, le_trans h31 h10, hpos, hdiff, hH₀,
    hH, hz₃, hz₅, 2.906, 100, -1.794, 1, one_pos, by norm_num, by norm_num, ?_,
    box_fails a t₅ t₃ t₀ h53 (le_trans h31 h10) hpos hdiff hH₀ hH hz₃ hz₅ _ _ _ _ (by norm_num)
      ?_ ?_⟩
  · rw [hz₅, lp4_eq _ _ _ _ _ _ x5_eq]
    exact mul_pos (div_pos (Real.log_pos (by norm_num)) one_pos) (by nlinarith)
  · nlinarith
  · rw [abs_of_pos (by nlinarith), abs_of_pos (by nlinarith)]; nlinarith

theorem l19_sq_box_h14 : necessity% Checked.Cosmography.B1L19.l19_sq_box 14 := by
  obtain ⟨a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH₀, hH, -, hz₃, hz₅⟩ :=
    Checked.Cosmography.B1FitWitness.exists_model
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := L_pows
  refine ⟨1 / 5, by norm_num, by norm_num, a, t₅, t₃, t₀, h53, le_trans h31 h10, hpos, hdiff, hH₀,
    hH, hz₃, hz₅, 2.906, 5.479, 100, 1, one_pos, by norm_num, by norm_num, ?_,
    box_fails a t₅ t₃ t₀ h53 (le_trans h31 h10) hpos hdiff hH₀ hH hz₃ hz₅ _ _ _ _ (by norm_num)
      ?_ ?_⟩
  · rw [hz₅, lp4_eq _ _ _ _ _ _ x5_eq]
    exact mul_pos (div_pos (Real.log_pos (by norm_num)) one_pos) (by nlinarith)
  · nlinarith
  · rw [abs_of_pos (by nlinarith), abs_of_pos (by nlinarith)]; nlinarith

theorem l19_sq_box_h15 : necessity% Checked.Cosmography.B1L19.l19_sq_box 15 := by
  obtain ⟨a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH₀, hH, -, hz₃, hz₅⟩ :=
    Checked.Cosmography.B1FitWitness.exists_model
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := L_pows
  refine ⟨1 / 5, by norm_num, by norm_num, a, t₅, t₃, t₀, h53, le_trans h31 h10, hpos, hdiff, hH₀,
    hH, hz₃, hz₅, 2.906, 5.479, -30, 1, one_pos, by norm_num, by norm_num, by norm_num,
    box_fails a t₅ t₃ t₀ h53 (le_trans h31 h10) hpos hdiff hH₀ hH hz₃ hz₅ _ _ _ _ (by norm_num)
      ?_ ?_⟩
  · nlinarith
  · rw [abs_of_pos (by nlinarith), abs_of_neg (by nlinarith)]; nlinarith

theorem l19_sqg_box_h11 : necessity% Checked.Cosmography.B1L19.l19_sqg_box 11 := by
  obtain ⟨a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH₀, hH, -, hz₃, hz₅⟩ :=
    Checked.Cosmography.B1FitWitness.exists_model
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := L_pows
  refine ⟨1 / 5, by norm_num, by norm_num, a, t₅, t₃, t₀, h53, le_trans h31 h10, hpos, hdiff, hH₀,
    hH, hz₃, hz₅, 3.043, 4.480, -30, -1, by norm_num, by norm_num, by norm_num, ?_,
    box_fails a t₅ t₃ t₀ h53 (le_trans h31 h10) hpos hdiff hH₀ hH hz₃ hz₅ _ _ _ _ (by norm_num)
      ?_ ?_⟩
  · rw [hz₅, lp4_eq _ _ _ _ _ _ x5_eq]
    apply mul_pos_of_neg_of_neg (div_neg_of_pos_of_neg (Real.log_pos (by norm_num)) (by norm_num))
    nlinarith
  · nlinarith
  · rw [abs_of_pos (by nlinarith), abs_of_neg (by nlinarith)]; nlinarith

theorem l19_sqg_box_h12 : necessity% Checked.Cosmography.B1L19.l19_sqg_box 12 := by
  obtain ⟨a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH₀, hH, -, hz₃, hz₅⟩ :=
    Checked.Cosmography.B1FitWitness.exists_model
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := L_pows
  refine ⟨1 / 5, by norm_num, by norm_num, a, t₅, t₃, t₀, h53, le_trans h31 h10, hpos, hdiff, hH₀,
    hH, hz₃, hz₅, -4, 4.480, -0.915, 1, one_pos, by norm_num, by norm_num, ?_,
    box_fails a t₅ t₃ t₀ h53 (le_trans h31 h10) hpos hdiff hH₀ hH hz₃ hz₅ _ _ _ _ (by norm_num)
      ?_ ?_⟩
  · rw [hz₅, lp4_eq _ _ _ _ _ _ x5_eq]
    exact mul_pos (div_pos (Real.log_pos (by norm_num)) one_pos) (by nlinarith)
  · nlinarith
  · rw [abs_of_pos (by nlinarith), abs_of_pos (by nlinarith)]; nlinarith

theorem l19_sqg_box_h13 : necessity% Checked.Cosmography.B1L19.l19_sqg_box 13 := by
  obtain ⟨a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH₀, hH, -, hz₃, hz₅⟩ :=
    Checked.Cosmography.B1FitWitness.exists_model
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := L_pows
  refine ⟨1 / 5, by norm_num, by norm_num, a, t₅, t₃, t₀, h53, le_trans h31 h10, hpos, hdiff, hH₀,
    hH, hz₃, hz₅, 3.043, 100, -0.915, 1, one_pos, by norm_num, by norm_num, ?_,
    box_fails a t₅ t₃ t₀ h53 (le_trans h31 h10) hpos hdiff hH₀ hH hz₃ hz₅ _ _ _ _ (by norm_num)
      ?_ ?_⟩
  · rw [hz₅, lp4_eq _ _ _ _ _ _ x5_eq]
    exact mul_pos (div_pos (Real.log_pos (by norm_num)) one_pos) (by nlinarith)
  · nlinarith
  · rw [abs_of_pos (by nlinarith), abs_of_pos (by nlinarith)]; nlinarith

theorem l19_sqg_box_h14 : necessity% Checked.Cosmography.B1L19.l19_sqg_box 14 := by
  obtain ⟨a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH₀, hH, -, hz₃, hz₅⟩ :=
    Checked.Cosmography.B1FitWitness.exists_model
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := L_pows
  refine ⟨1 / 5, by norm_num, by norm_num, a, t₅, t₃, t₀, h53, le_trans h31 h10, hpos, hdiff, hH₀,
    hH, hz₃, hz₅, 3.043, 4.480, 100, 1, one_pos, by norm_num, by norm_num, ?_,
    box_fails a t₅ t₃ t₀ h53 (le_trans h31 h10) hpos hdiff hH₀ hH hz₃ hz₅ _ _ _ _ (by norm_num)
      ?_ ?_⟩
  · rw [hz₅, lp4_eq _ _ _ _ _ _ x5_eq]
    exact mul_pos (div_pos (Real.log_pos (by norm_num)) one_pos) (by nlinarith)
  · nlinarith
  · rw [abs_of_pos (by nlinarith), abs_of_pos (by nlinarith)]; nlinarith

theorem l19_sqg_box_h15 : necessity% Checked.Cosmography.B1L19.l19_sqg_box 15 := by
  obtain ⟨a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH₀, hH, -, hz₃, hz₅⟩ :=
    Checked.Cosmography.B1FitWitness.exists_model
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := L_pows
  refine ⟨1 / 5, by norm_num, by norm_num, a, t₅, t₃, t₀, h53, le_trans h31 h10, hpos, hdiff, hH₀,
    hH, hz₃, hz₅, 3.043, 4.480, -30, 1, one_pos, by norm_num, by norm_num, by norm_num,
    box_fails a t₅ t₃ t₀ h53 (le_trans h31 h10) hpos hdiff hH₀ hH hz₃ hz₅ _ _ _ _ (by norm_num)
      ?_ ?_⟩
  · nlinarith
  · rw [abs_of_pos (by nlinarith), abs_of_neg (by nlinarith)]; nlinarith

end L19Box

section Curved
open Checked.Cosmography.BambaK Checked.Cosmography.B1L19 Checked.Cosmography.B1L19Curved

/-- The curved law's radicand is positive for `Ω ∈ [1/10, 1]`, `Ω₀ ∈ [1, 11/10]` and `1 + z > 0`. -/
theorem curved_arg_pos (Ω K₀ x : ℝ) (h0 : 1 / 10 ≤ Ω) (h1 : Ω ≤ 1) (hK0 : 1 ≤ K₀)
    (hK1 : K₀ ≤ 11 / 10) (hx : 0 < x) : 0 < Ω * x ^ 3 + (1 - K₀) * x ^ 2 + K₀ - Ω := by
  have hx3 : 0 < x ^ 3 := pow_pos hx 3
  have hx2 : 0 < x ^ 2 := pow_pos hx 2
  rcases le_or_gt x 1 with hle | hgt
  · have : 0 ≤ (K₀ - 1) * (1 - x ^ 2) := mul_nonneg (by linarith) (by nlinarith)
    nlinarith [mul_pos (show (0:ℝ) < Ω by linarith) hx3]
  · have : 0 < x ^ 2 * (Ω * x - (K₀ - 1)) := mul_pos hx2 (by nlinarith)
    nlinarith

theorem curved_model : ∃ (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ), t₅ ≤ t₃ ∧ t₃ ≤ t₀ ∧
    (∀ s ∈ Icc t₅ t₀, 0 < a s) ∧ (∀ s ∈ Icc t₅ t₀, DifferentiableAt ℝ a s) ∧
    0 < hubble a t₀ ∧ 1 ≤ omega0 0 a t₀ ∧ omega0 0 a t₀ ≤ 11 / 10 ∧
    (∀ s ∈ Icc t₅ t₀, hubble a s = hubble a t₀ * √(1 / 5 * (1 + redshift a t₀ s) ^ 3
        + (1 - omega0 0 a t₀) * (1 + redshift a t₀ s) ^ 2 + omega0 0 a t₀ - 1 / 5)) ∧
    redshift a t₀ t₃ = 2 * √2 - 1 ∧ redshift a t₀ t₅ = 4 * √2 - 1 := by
  obtain ⟨a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH₀, hH, _, hz₃, hz₅⟩ :=
    Checked.Cosmography.B1FitWitness.exists_model
  have hω : omega0 0 a t₀ = 1 := by simp [omega0]
  refine ⟨a, t₅, t₃, t₀, h53, le_trans h31 h10, hpos, hdiff, hH₀, by rw [hω], by rw [hω]; norm_num,
    fun s hs => ?_, hz₃, hz₅⟩
  rw [hω, hH s hs]
  congr 2
  ring

theorem curved_diff (Ω K : ℝ) (h0 : 1 / 10 ≤ Ω) (h1 : Ω ≤ 1) (a : ℝ → ℝ) (t₅ t₀ : ℝ)
    (hpos : ∀ s ∈ Icc t₅ t₀, 0 < a s) (hH₀ : 0 < hubble a t₀)
    (hK0 : 1 ≤ omega0 K a t₀) (hK1 : omega0 K a t₀ ≤ 11 / 10)
    (hH : ∀ s ∈ Icc t₅ t₀, hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3
        + (1 - omega0 K a t₀) * (1 + redshift a t₀ s) ^ 2 + omega0 K a t₀ - Ω)) :
    ∀ s ∈ Icc t₅ t₀, DifferentiableAt ℝ a s := by
  refine diff_of_law a t₅ t₀ (fun s => Ω * (1 + redshift a t₀ s) ^ 3
    + (1 - omega0 K a t₀) * (1 + redshift a t₀ s) ^ 2 + omega0 K a t₀ - Ω) hH₀ hH ?_
  intro s hs
  have ha₀ := hpos t₀ ⟨le_trans hs.1 hs.2, le_rfl⟩
  have has := hpos s hs
  have hy : 0 < 1 + redshift a t₀ s := by
    unfold redshift; have := div_pos ha₀ has; linarith
  exact curved_arg_pos Ω _ _ h0 h1 hK0 hK1 hy

theorem curved_H0 (Ω K : ℝ) (a : ℝ → ℝ) (t₅ t₀ : ℝ) (h50 : t₅ ≤ t₀)
    (hpos : ∀ s ∈ Icc t₅ t₀, 0 < a s) (hdiff : ∀ s ∈ Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH : ∀ s ∈ Icc t₅ t₀, hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3
        + (1 - omega0 K a t₀) * (1 + redshift a t₀ s) ^ 2 + omega0 K a t₀ - Ω))
    (hz : 0 < redshift a t₀ t₅) : 0 < hubble a t₀ :=
  H0_pos_of_redshift a t₅ t₀ t₅ (fun s => Ω * (1 + redshift a t₀ s) ^ 3
    + (1 - omega0 K a t₀) * (1 + redshift a t₀ s) ^ 2 + omega0 K a t₀ - Ω) ⟨le_rfl, h50⟩ hpos hdiff
    hH hz

theorem l19_sq_curved_r6 : dropped% Checked.Cosmography.B1L19Curved.l19_sq_curved 6 := by
  intro Ω K h0 h1 a t₅ t₃ t₀ h53 h30 hpos hH₀ hK0 hK1 hH hz3 hz5 H hHp
  exact l19_sq_curved Ω K h0 h1 a t₅ t₃ t₀ h53 h30 hpos
    (curved_diff Ω K h0 h1 a t₅ t₀ hpos hH₀ hK0 hK1 hH) hH₀ hK0 hK1 hH hz3 hz5 H hHp

theorem l19_sq_curved_r7 : dropped% Checked.Cosmography.B1L19Curved.l19_sq_curved 7 := by
  intro Ω K h0 h1 a t₅ t₃ t₀ h53 h30 hpos hdiff hK0 hK1 hH hz3 hz5 H hHp
  exact l19_sq_curved Ω K h0 h1 a t₅ t₃ t₀ h53 h30 hpos hdiff
    (curved_H0 Ω K a t₅ t₀ (le_trans h53 h30) hpos hdiff hH (hz5 ▸ z5_pos)) hK0 hK1 hH hz3 hz5 H hHp

theorem l19_sq_curved_h11 : necessity% Checked.Cosmography.B1L19Curved.l19_sq_curved 11 := by
  obtain ⟨a, t₅, t₃, t₀, h53, h30, hpos, hdiff, hH₀, hK0, hK1, hH, -, hz5⟩ := curved_model
  exact ⟨1 / 5, 0, by norm_num, by norm_num, a, t₅, t₅, t₀, le_rfl, le_trans h53 h30, hpos, hdiff,
    hH₀, hK0, hK1, hH, hz5, 1, one_pos, by rw [sub_self]; norm_num⟩

theorem l19_sq_curved_h12 : necessity% Checked.Cosmography.B1L19Curved.l19_sq_curved 12 := by
  obtain ⟨a, t₅, t₃, t₀, h53, h30, hpos, hdiff, hH₀, hK0, hK1, hH, hz3, -⟩ := curved_model
  have hsub : Icc t₃ t₀ ⊆ Icc t₅ t₀ := Icc_subset_Icc_left h53
  exact ⟨1 / 5, 0, by norm_num, by norm_num, a, t₃, t₃, t₀, le_rfl, h30,
    fun s hs => hpos s (hsub hs), fun s hs => hdiff s (hsub hs), hH₀, hK0, hK1,
    fun s hs => hH s (hsub hs), hz3, 1, one_pos, by rw [sub_self]; norm_num⟩

theorem l19_sq_curved_h13 : necessity% Checked.Cosmography.B1L19Curved.l19_sq_curved 13 := by
  obtain ⟨a, t₅, t₃, t₀, h53, h30, hpos, hdiff, hH₀, hK0, hK1, hH, hz3, hz5⟩ := curved_model
  exact ⟨1 / 5, 0, by norm_num, by norm_num, a, t₅, t₃, t₀, h53, h30, hpos, hdiff,
    hH₀, hK0, hK1, hH, hz3, hz5, 0, by norm_num [lp4_H0]⟩

theorem l19_sqg_curved_r6 : dropped% Checked.Cosmography.B1L19Curved.l19_sqg_curved 6 := by
  intro Ω K h0 h1 a t₅ t₃ t₀ h53 h30 hpos hH₀ hK0 hK1 hH hz3 hz5 H hHp
  exact l19_sqg_curved Ω K h0 h1 a t₅ t₃ t₀ h53 h30 hpos
    (curved_diff Ω K h0 h1 a t₅ t₀ hpos hH₀ hK0 hK1 hH) hH₀ hK0 hK1 hH hz3 hz5 H hHp

theorem l19_sqg_curved_r7 : dropped% Checked.Cosmography.B1L19Curved.l19_sqg_curved 7 := by
  intro Ω K h0 h1 a t₅ t₃ t₀ h53 h30 hpos hdiff hK0 hK1 hH hz3 hz5 H hHp
  exact l19_sqg_curved Ω K h0 h1 a t₅ t₃ t₀ h53 h30 hpos hdiff
    (curved_H0 Ω K a t₅ t₀ (le_trans h53 h30) hpos hdiff hH (hz5 ▸ z5_pos)) hK0 hK1 hH hz3 hz5 H hHp

theorem l19_sqg_curved_h11 : necessity% Checked.Cosmography.B1L19Curved.l19_sqg_curved 11 := by
  obtain ⟨a, t₅, t₃, t₀, h53, h30, hpos, hdiff, hH₀, hK0, hK1, hH, -, hz5⟩ := curved_model
  exact ⟨1 / 5, 0, by norm_num, by norm_num, a, t₅, t₅, t₀, le_rfl, le_trans h53 h30, hpos, hdiff,
    hH₀, hK0, hK1, hH, hz5, 1, one_pos, by rw [sub_self]; norm_num⟩

theorem l19_sqg_curved_h12 : necessity% Checked.Cosmography.B1L19Curved.l19_sqg_curved 12 := by
  obtain ⟨a, t₅, t₃, t₀, h53, h30, hpos, hdiff, hH₀, hK0, hK1, hH, hz3, -⟩ := curved_model
  have hsub : Icc t₃ t₀ ⊆ Icc t₅ t₀ := Icc_subset_Icc_left h53
  exact ⟨1 / 5, 0, by norm_num, by norm_num, a, t₃, t₃, t₀, le_rfl, h30,
    fun s hs => hpos s (hsub hs), fun s hs => hdiff s (hsub hs), hH₀, hK0, hK1,
    fun s hs => hH s (hsub hs), hz3, 1, one_pos, by rw [sub_self]; norm_num⟩

theorem l19_sqg_curved_h13 : necessity% Checked.Cosmography.B1L19Curved.l19_sqg_curved 13 := by
  obtain ⟨a, t₅, t₃, t₀, h53, h30, hpos, hdiff, hH₀, hK0, hK1, hH, hz3, hz5⟩ := curved_model
  exact ⟨1 / 5, 0, by norm_num, by norm_num, a, t₅, t₃, t₀, h53, h30, hpos, hdiff,
    hH₀, hK0, hK1, hH, hz3, hz5, 0, by norm_num [lp4_H0]⟩

end Curved

end Checked.Trust.NCL
