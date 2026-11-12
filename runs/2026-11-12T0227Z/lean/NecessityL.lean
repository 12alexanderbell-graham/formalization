import Checked.Trust.NonVacuity
import Checked.Cosmography.B1L19
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

end Checked.Trust.NCL
