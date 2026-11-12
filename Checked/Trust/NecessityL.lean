import Checked.Trust.NonVacuity
import Checked.Cosmography.B1L19
import Checked.Cosmography.B1Separation
import Checked.Cosmography.B1FitRL19
import Checked.Cosmography.B1L19Curved
import Checked.Fidelity.Pins
import Checked.Fidelity.FlatPins
import Checked.Fidelity.RedshiftCoeffSpecs
import Checked.Fidelity.YOmegaKSpecs
import Checked.Fidelity.FRSpecs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Hypothesis necessity, B1 family and pinning specifications (trust track T2b, run 2026-11-12T0227Z)

Scratch: `runs/2026-11-12T0227Z/lean/NecessityL.lean`. Witnesses for the fourteen B1 headlines (log-polynomial
luminosity-distance fits tested against flat ΛCDM, with and without curvature):
* differentiability of the scale factor and positivity of today's Hubble rate are REDUNDANT: the expansion law
  with a positive radicand forces differentiability (a junk derivative would make the Hubble rate vanish), and
  with a non-positive Hubble rate today the law makes the scale factor non-increasing, so no earlier source has
  positive redshift (`diff_of_law`, `H0_pos_of_redshift`);
* each source-redshift condition is NEEDED: moving one source onto the other makes the two residuals equal;
* the expansion law is NEEDED: the radiation-like model `a = √t` meets every other hypothesis and has `d_L = 2z`;
* a positive normalisation `H` is NEEDED where the statement allows `H = 0` (junk division makes every residual
  zero), and in the box theorems through a negative `H`;
* the coefficient box and the positivity at the far source of the two box theorems are NEEDED: in the exact
  ΛCDM model the far distance is at most four times the near one (`model_ratio`), and a quartic whose far value
  exceeds four times its near value makes the far residual no larger (`no_rise`);
* each residual condition of the separation pair is NEEDED: the ΛCDM coefficients match the remaining residual.

And for the twelve pinning theorems of `Checked/Fidelity/`: the specification hypothesis is NEEDED (a constant
function meets every other hypothesis and differs from the program definition in the static or de Sitter model);
for `hubbleSpec_pins`, `decelSpec_pins`, `yRedSpec_pins`, `omega0Spec_pins` and `curvKSpec_pins` the positivity, differentiability and nonzero-rate
conditions are NEEDED as well (the program definition shifted by one off that domain still meets the
specification), except differentiability in `omega0Spec_pins` and `curvKSpec_pins`, which is REDUNDANT (a nonzero
Hubble rate needs a genuine derivative).
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

/- Redshift conditions: with the `z = 2√2 − 1` source moved onto the `z = 4√2 − 1` source (or back), the
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

/- Redshift conditions of the separation pair: with both sources at the same redshift, the ΛCDM
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

theorem cubic_separation_h14 : necessity% Checked.Cosmography.B1Sep.cubic_separation 14 := by
  obtain ⟨a, t₇, t₃, t₀, h73, h30, hpos, hdiff, hH₀, hH, hz3, hz7⟩ := exists_flatLCDM_on
  have hsub : Icc t₃ t₀ ⊆ Icc t₇ t₀ := Icc_subset_Icc_left h73
  have hp3 := (cubic_misses_z3 (1 / 5) (by norm_num) (by norm_num) a t₃ t₀ h30
    (fun s hs => hpos s (hsub hs)) (fun s hs => hdiff s (hsub hs)) hH₀
    (fun s hs => hH s (hsub hs)) hz3).1
  have hp7 := (cubic_misses_z7 (1 / 5) (by norm_num) (by norm_num) a t₇ t₀ (le_trans h73 h30)
    hpos hdiff hH₀ hH hz7).1
  exact ⟨1 / 5, by norm_num, by norm_num, a, t₇, t₃, t₀, h73, h30, hpos, hdiff, hH₀, hH, hz3, hz7,
    lusA2 (1 / 5), lusA3 (1 / 5), hubble a t₀,
    5 * Real.logb 10 (lumDistFlat a t₀ t₇ / logPolyDL3 (lusA2 (1 / 5)) (lusA3 (1 / 5)) (hubble a t₀)
      (redshift a t₀ t₇)), hH₀, hp3, hp7, by rw [sub_self, abs_zero]; norm_num, by rw [sub_self, sub_self]; norm_num⟩

theorem cubic_separation_h15 : necessity% Checked.Cosmography.B1Sep.cubic_separation 15 := by
  obtain ⟨a, t₇, t₃, t₀, h73, h30, hpos, hdiff, hH₀, hH, hz3, hz7⟩ := exists_flatLCDM_on
  have hsub : Icc t₃ t₀ ⊆ Icc t₇ t₀ := Icc_subset_Icc_left h73
  have hp3 := (cubic_misses_z3 (1 / 5) (by norm_num) (by norm_num) a t₃ t₀ h30
    (fun s hs => hpos s (hsub hs)) (fun s hs => hdiff s (hsub hs)) hH₀
    (fun s hs => hH s (hsub hs)) hz3).1
  have hp7 := (cubic_misses_z7 (1 / 5) (by norm_num) (by norm_num) a t₇ t₀ (le_trans h73 h30)
    hpos hdiff hH₀ hH hz7).1
  exact ⟨1 / 5, by norm_num, by norm_num, a, t₇, t₃, t₀, h73, h30, hpos, hdiff, hH₀, hH, hz3, hz7,
    lusA2 (1 / 5), lusA3 (1 / 5), hubble a t₀,
    5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL3 (lusA2 (1 / 5)) (lusA3 (1 / 5)) (hubble a t₀)
      (redshift a t₀ t₃)), hH₀, hp3, hp7, by rw [sub_self, abs_zero]; norm_num, by rw [sub_self, sub_self]; norm_num⟩

theorem cubic_direction_h14 : necessity% Checked.Cosmography.B1Sep.cubic_direction 14 := by
  obtain ⟨a, t₇, t₃, t₀, h73, h30, hpos, hdiff, hH₀, hH, hz3, hz7⟩ := exists_flatLCDM_on
  have hsub : Icc t₃ t₀ ⊆ Icc t₇ t₀ := Icc_subset_Icc_left h73
  have hp3 := (cubic_misses_z3 (1 / 5) (by norm_num) (by norm_num) a t₃ t₀ h30
    (fun s hs => hpos s (hsub hs)) (fun s hs => hdiff s (hsub hs)) hH₀
    (fun s hs => hH s (hsub hs)) hz3).1
  have hp7 := (cubic_misses_z7 (1 / 5) (by norm_num) (by norm_num) a t₇ t₀ (le_trans h73 h30)
    hpos hdiff hH₀ hH hz7).1
  exact ⟨1 / 5, by norm_num, by norm_num, a, t₇, t₃, t₀, h73, h30, hpos, hdiff, hH₀, hH, hz3, hz7,
    lusA2 (1 / 5), lusA3 (1 / 5), hubble a t₀,
    5 * Real.logb 10 (lumDistFlat a t₀ t₇ / logPolyDL3 (lusA2 (1 / 5)) (lusA3 (1 / 5)) (hubble a t₀)
      (redshift a t₀ t₇)), hH₀, hp3, hp7, by rw [sub_self, abs_zero]; norm_num, by rw [sub_self, sub_self]; norm_num⟩

theorem cubic_direction_h15 : necessity% Checked.Cosmography.B1Sep.cubic_direction 15 := by
  obtain ⟨a, t₇, t₃, t₀, h73, h30, hpos, hdiff, hH₀, hH, hz3, hz7⟩ := exists_flatLCDM_on
  have hsub : Icc t₃ t₀ ⊆ Icc t₇ t₀ := Icc_subset_Icc_left h73
  have hp3 := (cubic_misses_z3 (1 / 5) (by norm_num) (by norm_num) a t₃ t₀ h30
    (fun s hs => hpos s (hsub hs)) (fun s hs => hdiff s (hsub hs)) hH₀
    (fun s hs => hH s (hsub hs)) hz3).1
  have hp7 := (cubic_misses_z7 (1 / 5) (by norm_num) (by norm_num) a t₇ t₀ (le_trans h73 h30)
    hpos hdiff hH₀ hH hz7).1
  exact ⟨1 / 5, by norm_num, by norm_num, a, t₇, t₃, t₀, h73, h30, hpos, hdiff, hH₀, hH, hz3, hz7,
    lusA2 (1 / 5), lusA3 (1 / 5), hubble a t₀,
    5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL3 (lusA2 (1 / 5)) (lusA3 (1 / 5)) (hubble a t₀)
      (redshift a t₀ t₃)), hH₀, hp3, hp7, by rw [sub_self, abs_zero]; norm_num, by rw [sub_self, sub_self]; norm_num⟩

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

/- Coefficient conditions of the two box theorems. In the exact flat ΛCDM model at `Ω = 1/5` the two
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

section Radiation
open Checked.Cosmography.B1 Checked.Cosmography.B1L19 Checked.Cosmography.B1Fit
  Checked.Cosmography.BambaY

/- The expansion law is needed: the radiation-like model `a(t) = √t` (`H = 1/(2t)`, observed at
`t₀ = 1`) meets every other hypothesis (positivity, differentiability, `H(t₀) = 1/2 > 0`, the source
redshifts), and its luminosity distance is exactly `d_L = 2z`; with it the claimed residual
differences fail. -/

theorem rad_hasDeriv (t : ℝ) (ht : 0 < t) : HasDerivAt (fun s : ℝ => √s) (1 / (2 * √t)) t :=
  Real.hasDerivAt_sqrt ht.ne'

theorem rad_hubble (t : ℝ) (ht : 0 < t) : hubble (fun s : ℝ => √s) t = 1 / (2 * t) := by
  unfold hubble
  rw [(rad_hasDeriv t ht).deriv]
  have h := Real.sqrt_pos.2 ht
  have h2 := Real.mul_self_sqrt ht.le
  field_simp
  nlinarith

theorem rad_pos (t₅ : ℝ) (h : 0 < t₅) : ∀ s ∈ Icc t₅ 1, 0 < (fun s : ℝ => √s) s :=
  fun s hs => Real.sqrt_pos.2 (lt_of_lt_of_le h hs.1)

theorem rad_diff (t₅ : ℝ) (h : 0 < t₅) : ∀ s ∈ Icc t₅ 1, DifferentiableAt ℝ (fun s : ℝ => √s) s :=
  fun s hs => (rad_hasDeriv s (lt_of_lt_of_le h hs.1)).differentiableAt

theorem rad_H0 : 0 < hubble (fun s : ℝ => √s) 1 := by rw [rad_hubble 1 one_pos]; norm_num

theorem rad_dL (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    lumDistFlat (fun s : ℝ => √s) 1 t = 2 * redshift (fun s : ℝ => √s) 1 t := by
  have hint : ∫ s in t..1, 1 / (fun s : ℝ => √s) s = 2 * √1 - 2 * √t := by
    have hderiv : ∀ x ∈ uIcc t 1, HasDerivAt (fun s : ℝ => 2 * √s) (1 / √x) x := by
      intro x hx
      rw [uIcc_of_le ht1] at hx
      have hx0 : 0 < x := lt_of_lt_of_le ht hx.1
      have := (rad_hasDeriv x hx0).const_mul 2
      convert this using 1
      have := Real.sqrt_pos.2 hx0
      field_simp
    have hcont : ContinuousOn (fun s : ℝ => 1 / √s) (uIcc t 1) := by
      intro x hx
      rw [uIcc_of_le ht1] at hx
      have hx0 : 0 < x := lt_of_lt_of_le ht hx.1
      exact (continuousAt_const.div Real.continuous_sqrt.continuousAt
        (Real.sqrt_pos.2 hx0).ne').continuousWithinAt
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)
  have hs := Real.sqrt_pos.2 ht
  simp only [lumDistFlat, comoving, redshift] at *
  rw [hint, Real.sqrt_one]
  field_simp
  ring

theorem rad_z (u : ℝ) (hu : 0 < u) : redshift (fun s : ℝ => √s) 1 (1 / u ^ 2) = u - 1 := by
  simp only [redshift, Real.sqrt_one]
  rw [Real.sqrt_div' 1 (sq_nonneg u), Real.sqrt_one, Real.sqrt_sq hu.le]
  field_simp

theorem t3_eq : (1 / 8 : ℝ) = 1 / (2 * √2) ^ 2 := by
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num

theorem t5_eq : (1 / 32 : ℝ) = 1 / (4 * √2) ^ 2 := by
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num

theorem rad_z3 : redshift (fun s : ℝ => √s) 1 (1 / 8) = 2 * √2 - 1 := by
  rw [t3_eq]; exact rad_z _ (by positivity)

theorem rad_z5 : redshift (fun s : ℝ => √s) 1 (1 / 32) = 4 * √2 - 1 := by
  rw [t5_eq]; exact rad_z _ (by positivity)

/-- `5 log₁₀ A − 5 log₁₀ B ≤ 5e/2.3` when `A/B ≤ 1 + e`. -/
theorem five_logb_diff_le (A B e : ℝ) (hA : 0 < A) (hB : 0 < B) (he0 : 0 ≤ e) (he : A / B ≤ 1 + e) :
    5 * Real.logb 10 A - 5 * Real.logb 10 B ≤ 5 * e / (23 / 10) := by
  have hl := log_ten_ge
  have hl0 : 0 < Real.log 10 := by linarith
  have hAB : 0 < A / B := div_pos hA hB
  have h1 : Real.log (A / B) ≤ A / B - 1 := Real.log_le_sub_one_of_pos hAB
  rw [← mul_sub, ← Real.logb_div hA.ne' hB.ne', Real.logb]
  have h2 : Real.log (A / B) / Real.log 10 ≤ e / (23 / 10) := by
    rcases le_or_gt (Real.log (A / B)) 0 with h | h
    · have : Real.log (A / B) / Real.log 10 ≤ 0 := div_nonpos_of_nonpos_of_nonneg h hl0.le
      linarith [div_nonneg he0 (by norm_num : (0:ℝ) ≤ 23 / 10)]
    · rw [div_le_div_iff₀ hl0 (by norm_num)]
      nlinarith
  linarith

/-- The radiation model's residual difference for any quartic positive at both redshifts. -/
theorem rad_diff_le (a₂ a₃ a₄ e : ℝ) (he0 : 0 ≤ e) (lumD : ℝ → ℝ)
    (hd3 : lumD (1 / 8) = 2 * (2 * √2 - 1)) (hd5 : lumD (1 / 32) = 2 * (4 * √2 - 1))
    (hQ3 : 0 < 3 / 2 * (Real.log 2 / Real.log 10) + a₂ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + a₃ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + a₄ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4)
    (hQ5 : 0 < 5 / 2 * (Real.log 2 / Real.log 10) + a₂ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + a₃ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + a₄ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 4)
    (hX : (4 * √2 - 1) * (3 / 2 * (Real.log 2 / Real.log 10)
        + a₂ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
        + a₃ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + a₄ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4)
      ≤ (1 + e) * ((2 * √2 - 1) * (5 / 2 * (Real.log 2 / Real.log 10)
        + a₂ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 2
        + a₃ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 3
        + a₄ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 4))) :
    5 * Real.logb 10 (lumD (1 / 32) / logPolyDL4 a₂ a₃ a₄ 1
        (redshift (fun s : ℝ => √s) 1 (1 / 32)))
      - 5 * Real.logb 10 (lumD (1 / 8) / logPolyDL4 a₂ a₃ a₄ 1
        (redshift (fun s : ℝ => √s) 1 (1 / 8))) ≤ 5 * e / (23 / 10) := by
  rw [rad_z3, rad_z5, lp4_eq _ _ _ _ _ _ x3_eq, lp4_eq _ _ _ _ _ _ x5_eq, hd3, hd5]
  have hz3 := z3_pos
  have hz5 := z5_pos
  have hl0 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  set Q3 := 3 / 2 * (Real.log 2 / Real.log 10) + a₂ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + a₃ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + a₄ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4
  set Q5 := 5 / 2 * (Real.log 2 / Real.log 10) + a₂ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + a₃ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + a₄ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 4
  apply five_logb_diff_le _ _ e (by positivity) (by positivity) he0
  rw [div_div_div_eq, div_le_iff₀ (by positivity)]
  rw [div_one]
  nlinarith [mul_le_mul_of_nonneg_left hX (show (0:ℝ) ≤ 2 * Real.log 10 by linarith)]

theorem chain_le (z5 Q3 u5 U3 z3 Q5 l3 L5 k : ℝ) (h1 : 0 ≤ z5) (h2 : z5 ≤ u5) (h3 : 0 ≤ Q3)
    (h4 : Q3 ≤ U3) (h5 : l3 ≤ z3) (h6 : L5 ≤ Q5) (h7 : 0 ≤ l3) (h8 : 0 ≤ L5)
    (h9 : u5 * U3 ≤ k * (l3 * L5)) (hk : 0 ≤ k) : z5 * Q3 ≤ k * (z3 * Q5) := by
  have a1 : z5 * Q3 ≤ u5 * U3 := mul_le_mul h2 h4 h3 (le_trans h1 h2)
  have a2 : l3 * L5 ≤ z3 * Q5 := mul_le_mul h5 h6 h8 (le_trans h7 h5)
  nlinarith [mul_le_mul_of_nonneg_left a2 hk]

theorem rad_lumDist (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    Checked.Cosmography.BambaK.lumDist 0 (fun s : ℝ => √s) 1 t
      = 2 * redshift (fun s : ℝ => √s) 1 t := by
  rw [← rad_dL t ht ht1]
  simp [Checked.Cosmography.BambaK.lumDist, lumDistFlat, Checked.Cosmography.Transverse.transverse]

theorem rad_omega0 : Checked.Cosmography.BambaK.omega0 0 (fun s : ℝ => √s) 1 = 1 := by
  simp [Checked.Cosmography.BambaK.omega0]

theorem l19_sq_central_h8 : necessity% Checked.Cosmography.B1L19.l19_sq_central 8 := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := L_pows
  obtain ⟨q1, q2⟩ := sqrt2_bounds
  have hQ3 : 0 < 3 / 2 * (Real.log 2 / Real.log 10) + (3.075) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + (4.466) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + (-3.716) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4 := by nlinarith
  have hQ5 : 3.2050 ≤ 5 / 2 * (Real.log 2 / Real.log 10) + (3.075) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + (4.466) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + (-3.716) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 4 := by nlinarith
  have hU3 : 3 / 2 * (Real.log 2 / Real.log 10) + (3.075) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + (4.466) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + (-3.716) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4 ≤ 1.3360 := by nlinarith
  have hD := rad_diff_le (3.075) (4.466) (-3.716) (1 / 10) (by norm_num) (lumDistFlat (fun s : ℝ => √s) 1) (by rw [rad_dL _ (by norm_num) (by norm_num), rad_z3])
    (by rw [rad_dL _ (by norm_num) (by norm_num), rad_z5]) hQ3 (by linarith)
    (chain_le _ _ (4 * 1.41421357 - 1) 1.3360 _ _ (2 * 1.41421356 - 1) 3.2050 _ (by linarith) (by linarith)
      hQ3.le hU3 (by linarith) hQ5 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  refine ⟨1 / 5, by norm_num, by norm_num, fun s : ℝ => √s, 1 / 32, 1 / 8, 1, by norm_num, by norm_num,
    rad_pos _ (by norm_num), rad_diff _ (by norm_num), rad_H0, rad_z3, rad_z5, 1, one_pos, ?_⟩
  norm_num at hD ⊢; linarith

theorem l19_sqg_central_h8 : necessity% Checked.Cosmography.B1L19.l19_sqg_central 8 := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := L_pows
  obtain ⟨q1, q2⟩ := sqrt2_bounds
  have hQ3 : 0 < 3 / 2 * (Real.log 2 / Real.log 10) + (3.205) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + (3.564) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + (-2.510) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4 := by nlinarith
  have hQ5 : 3.281 ≤ 5 / 2 * (Real.log 2 / Real.log 10) + (3.205) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + (3.564) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + (-2.510) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 4 := by nlinarith
  have hU3 : 3 / 2 * (Real.log 2 / Real.log 10) + (3.205) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + (3.564) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + (-2.510) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4 ≤ 1.3295 := by nlinarith
  have hD := rad_diff_le (3.205) (3.564) (-2.510) (6 / 100) (by norm_num) (lumDistFlat (fun s : ℝ => √s) 1) (by rw [rad_dL _ (by norm_num) (by norm_num), rad_z3])
    (by rw [rad_dL _ (by norm_num) (by norm_num), rad_z5]) hQ3 (by linarith)
    (chain_le _ _ (4 * 1.41421357 - 1) 1.3295 _ _ (2 * 1.41421356 - 1) 3.281 _ (by linarith) (by linarith)
      hQ3.le hU3 (by linarith) hQ5 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  refine ⟨1 / 5, by norm_num, by norm_num, fun s : ℝ => √s, 1 / 32, 1 / 8, 1, by norm_num, by norm_num,
    rad_pos _ (by norm_num), rad_diff _ (by norm_num), rad_H0, rad_z3, rad_z5, 1, one_pos, ?_⟩
  norm_num at hD ⊢; linarith

theorem l19_sq_curved_h10 : necessity% Checked.Cosmography.B1L19Curved.l19_sq_curved 10 := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := L_pows
  obtain ⟨q1, q2⟩ := sqrt2_bounds
  have hQ3 : 0 < 3 / 2 * (Real.log 2 / Real.log 10) + (3.075) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + (4.466) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + (-3.716) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4 := by nlinarith
  have hQ5 : 3.2050 ≤ 5 / 2 * (Real.log 2 / Real.log 10) + (3.075) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + (4.466) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + (-3.716) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 4 := by nlinarith
  have hU3 : 3 / 2 * (Real.log 2 / Real.log 10) + (3.075) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + (4.466) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + (-3.716) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4 ≤ 1.3360 := by nlinarith
  have hD := rad_diff_le (3.075) (4.466) (-3.716) (1 / 10) (by norm_num) (Checked.Cosmography.BambaK.lumDist 0 (fun s : ℝ => √s) 1) (by rw [rad_lumDist _ (by norm_num) (by norm_num), rad_z3])
    (by rw [rad_lumDist _ (by norm_num) (by norm_num), rad_z5]) hQ3 (by linarith)
    (chain_le _ _ (4 * 1.41421357 - 1) 1.3360 _ _ (2 * 1.41421356 - 1) 3.2050 _ (by linarith) (by linarith)
      hQ3.le hU3 (by linarith) hQ5 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  refine ⟨1 / 5, 0, by norm_num, by norm_num, fun s : ℝ => √s, 1 / 32, 1 / 8, 1, by norm_num, by norm_num,
    rad_pos _ (by norm_num), rad_diff _ (by norm_num), rad_H0, by rw [rad_omega0], by rw [rad_omega0]; norm_num, rad_z3, rad_z5, 1, one_pos, ?_⟩
  norm_num at hD ⊢; linarith

theorem l19_sqg_curved_h10 : necessity% Checked.Cosmography.B1L19Curved.l19_sqg_curved 10 := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := L_pows
  obtain ⟨q1, q2⟩ := sqrt2_bounds
  have hQ3 : 0 < 3 / 2 * (Real.log 2 / Real.log 10) + (3.205) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + (3.564) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + (-2.510) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4 := by nlinarith
  have hQ5 : 3.281 ≤ 5 / 2 * (Real.log 2 / Real.log 10) + (3.205) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + (3.564) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + (-2.510) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 4 := by nlinarith
  have hU3 : 3 / 2 * (Real.log 2 / Real.log 10) + (3.205) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + (3.564) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + (-2.510) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4 ≤ 1.3295 := by nlinarith
  have hD := rad_diff_le (3.205) (3.564) (-2.510) (6 / 100) (by norm_num) (Checked.Cosmography.BambaK.lumDist 0 (fun s : ℝ => √s) 1) (by rw [rad_lumDist _ (by norm_num) (by norm_num), rad_z3])
    (by rw [rad_lumDist _ (by norm_num) (by norm_num), rad_z5]) hQ3 (by linarith)
    (chain_le _ _ (4 * 1.41421357 - 1) 1.3295 _ _ (2 * 1.41421356 - 1) 3.281 _ (by linarith) (by linarith)
      hQ3.le hU3 (by linarith) hQ5 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  refine ⟨1 / 5, 0, by norm_num, by norm_num, fun s : ℝ => √s, 1 / 32, 1 / 8, 1, by norm_num, by norm_num,
    rad_pos _ (by norm_num), rad_diff _ (by norm_num), rad_H0, by rw [rad_omega0], by rw [rad_omega0]; norm_num, rad_z3, rad_z5, 1, one_pos, ?_⟩
  norm_num at hD ⊢; linarith

theorem l19_sq_box_h8 : necessity% Checked.Cosmography.B1L19.l19_sq_box 8 := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := L_pows
  obtain ⟨q1, q2⟩ := sqrt2_bounds
  have hQ3 : 0 < 3 / 2 * (Real.log 2 / Real.log 10) + (31 / 10) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + (4) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + (-2) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4 := by nlinarith
  have hQ5 : 3.571 ≤ 5 / 2 * (Real.log 2 / Real.log 10) + (31 / 10) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + (4) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + (-2) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 4 := by nlinarith
  have hU3 : 3 / 2 * (Real.log 2 / Real.log 10) + (31 / 10) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + (4) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + (-2) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4 ≤ 1.3695 := by nlinarith
  have hD := rad_diff_le (31 / 10) (4) (-2) (0) (by norm_num) (lumDistFlat (fun s : ℝ => √s) 1) (by rw [rad_dL _ (by norm_num) (by norm_num), rad_z3])
    (by rw [rad_dL _ (by norm_num) (by norm_num), rad_z5]) hQ3 (by linarith)
    (chain_le _ _ (4 * 1.41421357 - 1) 1.3695 _ _ (2 * 1.41421356 - 1) 3.571 _ (by linarith) (by linarith)
      hQ3.le hU3 (by linarith) hQ5 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  refine ⟨1 / 5, by norm_num, by norm_num, fun s : ℝ => √s, 1 / 32, 1 / 8, 1, by norm_num, by norm_num,
    rad_pos _ (by norm_num), rad_diff _ (by norm_num), rad_H0, rad_z3, rad_z5, 31 / 10, 4, -2, 1, one_pos, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [rad_z5]
    exact quartic_pos5 _ _ _ 1 one_pos (31 / 10) 4 (-2) le_rfl le_rfl le_rfl (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · norm_num at hD ⊢; linarith

theorem l19_sqg_box_h8 : necessity% Checked.Cosmography.B1L19.l19_sqg_box 8 := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := L_pows
  obtain ⟨q1, q2⟩ := sqrt2_bounds
  have hQ3 : 0 < 3 / 2 * (Real.log 2 / Real.log 10) + (31 / 10) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + (4) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + (-2) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4 := by nlinarith
  have hQ5 : 3.571 ≤ 5 / 2 * (Real.log 2 / Real.log 10) + (31 / 10) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + (4) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + (-2) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 4 := by nlinarith
  have hU3 : 3 / 2 * (Real.log 2 / Real.log 10) + (31 / 10) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + (4) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + (-2) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4 ≤ 1.3695 := by nlinarith
  have hD := rad_diff_le (31 / 10) (4) (-2) (0) (by norm_num) (lumDistFlat (fun s : ℝ => √s) 1) (by rw [rad_dL _ (by norm_num) (by norm_num), rad_z3])
    (by rw [rad_dL _ (by norm_num) (by norm_num), rad_z5]) hQ3 (by linarith)
    (chain_le _ _ (4 * 1.41421357 - 1) 1.3695 _ _ (2 * 1.41421356 - 1) 3.571 _ (by linarith) (by linarith)
      hQ3.le hU3 (by linarith) hQ5 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  refine ⟨1 / 5, by norm_num, by norm_num, fun s : ℝ => √s, 1 / 32, 1 / 8, 1, by norm_num, by norm_num,
    rad_pos _ (by norm_num), rad_diff _ (by norm_num), rad_H0, rad_z3, rad_z5, 31 / 10, 4, -2, 1, one_pos, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [rad_z5]
    exact quartic_pos5 _ _ _ 1 one_pos (31 / 10) 4 (-2) le_rfl le_rfl le_rfl (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · norm_num at hD ⊢; linarith

theorem logb4 : Real.logb 10 (1 + 3) = 2 * Real.log 2 / Real.log 10 := by
  rw [show (1:ℝ) + 3 = 2 ^ 2 by norm_num, Real.logb, Real.log_pow]; push_cast; ring

theorem logb8 : Real.logb 10 (1 + 7) = 3 * Real.log 2 / Real.log 10 := by
  rw [show (1:ℝ) + 7 = 2 ^ 3 by norm_num, Real.logb, Real.log_pow]; push_cast; ring

theorem rad_P3 : logPolyDL3 (lusA2 (1 / 5)) (lusA3 (1 / 5)) (hubble (fun s : ℝ => √s) 1) 3
    = 4 * Real.log 2 + 54 / 5 * Real.log 2 ^ 2 + 974 / 75 * Real.log 2 ^ 3 := by
  have hl0 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  rw [rad_hubble 1 one_pos]
  simp only [logPolyDL3, lusA2, lusA3, logb4]
  field_simp
  ring

theorem rad_P7 : logPolyDL3 (lusA2 (1 / 5)) (lusA3 (1 / 5)) (hubble (fun s : ℝ => √s) 1) 7
    = 6 * Real.log 2 + 243 / 10 * Real.log 2 ^ 2 + 4383 / 100 * Real.log 2 ^ 3 := by
  have hl0 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  rw [rad_hubble 1 one_pos]
  simp only [logPolyDL3, lusA2, lusA3, logb8]
  field_simp
  ring

theorem rad_zk (k : ℝ) (hk : 0 < k) : redshift (fun s : ℝ => √s) 1 (1 / (1 + k) ^ 2) = k :=
  by rw [rad_z _ (by linarith)]; ring

theorem logb_le_zero_of (A : ℝ) (hA : 0 < A) (h : A ≤ 1) : Real.logb 10 A ≤ 0 :=
  Real.logb_nonpos (by norm_num) hA.le h

theorem cubic_misses_z3_h7 : necessity% Checked.Cosmography.B1.cubic_misses_z3 7 := by
  have hz : redshift (fun s : ℝ => √s) 1 (1 / 16) = 3 := by
    rw [show (1 / 16 : ℝ) = 1 / (1 + 3) ^ 2 by norm_num]; exact rad_zk 3 (by norm_num)
  have hl := Real.log_two_gt_d9
  refine ⟨1 / 5, by norm_num, by norm_num, fun s : ℝ => √s, 1 / 16, 1, by norm_num,
    rad_pos _ (by norm_num), rad_diff _ (by norm_num), rad_H0, hz, ?_⟩
  rintro ⟨-, h⟩
  rw [hz, rad_P3, rad_dL _ (by norm_num) (by norm_num), hz] at h
  have hP : 0 < 4 * Real.log 2 + 54 / 5 * Real.log 2 ^ 2 + 974 / 75 * Real.log 2 ^ 3 := by positivity
  have := logb_le_zero_of (2 * 3 / (4 * Real.log 2 + 54 / 5 * Real.log 2 ^ 2 + 974 / 75 * Real.log 2 ^ 3))
    (div_pos (by norm_num) hP) ((div_le_one hP).2 (by nlinarith))
  linarith

theorem cubic_misses_z7_h7 : necessity% Checked.Cosmography.B1.cubic_misses_z7 7 := by
  have hz : redshift (fun s : ℝ => √s) 1 (1 / 64) = 7 := by
    rw [show (1 / 64 : ℝ) = 1 / (1 + 7) ^ 2 by norm_num]; exact rad_zk 7 (by norm_num)
  have hl := Real.log_two_gt_d9
  refine ⟨1 / 5, by norm_num, by norm_num, fun s : ℝ => √s, 1 / 64, 1, by norm_num,
    rad_pos _ (by norm_num), rad_diff _ (by norm_num), rad_H0, hz, ?_⟩
  rintro ⟨-, h⟩
  rw [hz, rad_P7, rad_dL _ (by norm_num) (by norm_num), hz] at h
  have hP : 0 < 6 * Real.log 2 + 243 / 10 * Real.log 2 ^ 2 + 4383 / 100 * Real.log 2 ^ 3 := by
    positivity
  have := logb_le_zero_of (2 * 7 / (6 * Real.log 2 + 243 / 10 * Real.log 2 ^ 2
    + 4383 / 100 * Real.log 2 ^ 3)) (div_pos (by norm_num) hP) ((div_le_one hP).2 (by nlinarith))
  linarith

theorem cubic_shape_miss_h8 : necessity% Checked.Cosmography.B1.cubic_shape_miss 8 := by
  have hz3 : redshift (fun s : ℝ => √s) 1 (1 / 16) = 3 := by
    rw [show (1 / 16 : ℝ) = 1 / (1 + 3) ^ 2 by norm_num]; exact rad_zk 3 (by norm_num)
  have hz7 : redshift (fun s : ℝ => √s) 1 (1 / 64) = 7 := by
    rw [show (1 / 64 : ℝ) = 1 / (1 + 7) ^ 2 by norm_num]; exact rad_zk 7 (by norm_num)
  have hl := Real.log_two_gt_d9
  have hl' := Real.log_two_lt_d9
  refine ⟨1 / 5, by norm_num, by norm_num, fun s : ℝ => √s, 1 / 64, 1 / 16, 1, by norm_num,
    by norm_num, rad_pos _ (by norm_num), rad_diff _ (by norm_num), rad_H0, hz3, hz7, ?_⟩
  rw [hz3, hz7, rad_P3, rad_P7, rad_dL _ (by norm_num) (by norm_num),
    rad_dL _ (by norm_num) (by norm_num), hz3, hz7]
  set l := Real.log 2
  have hP3 : 0 < 4 * l + 54 / 5 * l ^ 2 + 974 / 75 * l ^ 3 := by positivity
  have hP7 : 0 < 6 * l + 243 / 10 * l ^ 2 + 4383 / 100 * l ^ 3 := by positivity
  have hD := five_logb_diff_le (2 * 7 / (6 * l + 243 / 10 * l ^ 2 + 4383 / 100 * l ^ 3))
    (2 * 3 / (4 * l + 54 / 5 * l ^ 2 + 974 / 75 * l ^ 3)) 0 (by positivity) (by positivity) le_rfl
    (by rw [div_div_div_eq, div_le_iff₀ (by positivity)]; nlinarith)
  norm_num at hD ⊢; linarith

theorem lumDistFlat_flatLCDM_h7 : necessity% Checked.Cosmography.B1.lumDistFlat_flatLCDM 7 := by
  have hz : redshift (fun s : ℝ => √s) 1 (1 / 16) = 3 := by
    rw [show (1 / 16 : ℝ) = 1 / (1 + 3) ^ 2 by norm_num]; exact rad_zk 3 (by norm_num)
  refine ⟨1, le_rfl.trans' zero_le_one, le_rfl, fun s : ℝ => √s, 1 / 16, 1, by norm_num,
    rad_pos _ (by norm_num), rad_diff _ (by norm_num), rad_H0, ?_⟩
  rw [rad_dL _ (by norm_num) (by norm_num), hz, rad_hubble 1 one_pos]
  have e1 : √((fun s : ℝ => √s) (1 / 16) / (fun s : ℝ => √s) 1) = 1 / 2 := by
    simp only [Real.sqrt_one, div_one]
    rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num),
      show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [e1]
  simp
  norm_num

end Radiation

section Pins
open Checked.Cosmography.BambaK Checked.Cosmography.BambaY Checked.Cosmography.BambaA
  Checked.Cosmography.BambaZ Checked.Cosmography.FRCosmo Checked.Cosmography.Aviles
  Checked.Cosmography.Transverse

/- The specification hypothesis of each pinning theorem is needed: a constant function (value `7`) meets
every other hypothesis (static model `a ≡ 1`, or de Sitter `a = exp` at `t = 0`) and differs from the
program definition there. -/

theorem const_comoving : comoving (fun _ : ℝ => (1 : ℝ)) 0 (-1) = 1 := by simp [comoving]

theorem const_redshift (t₀ t : ℝ) : redshift (fun _ : ℝ => (1 : ℝ)) t₀ t = 0 := by simp [redshift]

theorem const_lumDist : lumDist 0 (fun _ : ℝ => (1 : ℝ)) 0 (-1) = 1 := by
  simp [lumDist, const_redshift, transverse, const_comoving]

theorem exp_hubble : hubble Real.exp = fun _ => 1 := by
  funext t; simp [hubble, Real.deriv_exp]

theorem lumDistSpec2_pins_h1 : necessity% Checked.Fidelity.lumDistSpec2_pins 1 :=
  ⟨fun _ _ _ _ => 7, 0, fun _ => 1, 0, -1, by norm_num, fun _ _ => one_pos, continuousOn_const,
    by rw [const_lumDist]; norm_num⟩

theorem angDistSpec_pins_h1 : necessity% Checked.Fidelity.angDistSpec_pins 1 :=
  ⟨fun _ _ _ _ => 7, 0, fun _ => 1, 0, -1, by norm_num, fun _ _ => one_pos, continuousOn_const,
    by simp [angDist, const_lumDist, const_redshift]⟩

theorem lumDistFlat_pins_h1 : necessity% Checked.Fidelity.lumDistFlat_pins 1 :=
  ⟨fun _ _ _ _ => 7, fun _ => 1, 0, -1, by norm_num, fun _ _ => one_pos, continuousOn_const,
    by simp [lumDistFlat, const_redshift, const_comoving]⟩

theorem comoving_pins_h1 : necessity% Checked.Fidelity.comoving_pins 1 :=
  ⟨fun _ _ _ _ => 7, fun _ => 1, 0, -1, by norm_num, fun _ _ => one_pos, continuousOn_const,
    by simp [const_redshift, const_comoving]⟩

theorem hubbleSpec_pins_h1 : necessity% Checked.Fidelity.hubbleSpec_pins 1 :=
  ⟨fun _ _ => 7, Real.exp, 0, Real.exp_pos 0, Real.differentiableAt_exp,
    by rw [exp_hubble]; norm_num⟩

theorem decelSpec_pins_h1 : necessity% Checked.Fidelity.decelSpec_pins 1 :=
  ⟨fun _ _ => 7, Real.exp, Real.exp, Real.exp 0, 0,
    Filter.Eventually.of_forall fun s => Real.hasDerivAt_exp s, Real.hasDerivAt_exp 0,
    Real.exp_pos 0, (Real.exp_pos 0).ne', by simp [decel, Real.deriv_exp]; norm_num⟩

theorem redshiftCore_pins_h1 : necessity% Checked.Fidelity.redshiftCore_pins 1 :=
  ⟨fun _ _ _ => 7, fun _ => 1, 0, 0, ⟨fun _ _ => one_pos, contDiffOn_const⟩,
    by rw [const_redshift]; norm_num⟩

theorem cosmoCoeffCore_pins_h1 : necessity% Checked.Fidelity.cosmoCoeffCore_pins 1 :=
  ⟨fun _ _ _ => 7, 1, Real.exp, 0,
    ⟨Real.exp_pos 0, Real.contDiff_exp.contDiffAt, by simp [Real.deriv_exp]⟩,
    by simp [cosmoCoeff, exp_hubble, iteratedDeriv_one, Real.deriv_exp]⟩

theorem yRedSpec_pins_h1 : necessity% Checked.Fidelity.yRedSpec_pins 1 :=
  ⟨fun _ _ _ => 7, fun _ => 1, 0, -1, one_pos, one_pos,
    by simp [yred, const_redshift]⟩

theorem omega0Spec_pins_h1 : necessity% Checked.Fidelity.omega0Spec_pins 1 :=
  ⟨fun _ _ _ => 7, 0, Real.exp, 0, Real.exp_pos 0, Real.differentiableAt_exp,
    by simp [Real.deriv_exp], by simp [omega0, exp_hubble]⟩

theorem curvKSpec_pins_h1 : necessity% Checked.Fidelity.curvKSpec_pins 1 :=
  ⟨fun _ _ _ => 7, 1, Real.exp, 0, Real.exp_pos 0, Real.differentiableAt_exp,
    by simp [Real.deriv_exp], by simp [curvK, exp_hubble]⟩

theorem ricciSpec_pins_h1 : necessity% Checked.Fidelity.ricciSpec_pins 1 :=
  ⟨fun _ _ => 7, Real.exp, Real.exp, Real.exp, 0, Real.exp_pos 0,
    Filter.Eventually.of_forall fun s => Real.hasDerivAt_exp s, Real.hasDerivAt_exp 0,
    by simp [curv, exp_hubble]; norm_num⟩

/- `HubbleSpec` constrains its function only where `a t > 0` and `a` is differentiable at `t`, so the Hubble
rate shifted by one off that domain meets the specification; it differs from `hubble` for the contracting
`a = −exp` (negative scale factor) and for `a = 1 + |t|` at `0` (not differentiable). -/

open Classical in
noncomputable def hubbleOff (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  if 0 < a t ∧ DifferentiableAt ℝ a t then hubble a t else hubble a t + 1

theorem hubbleOff_spec : Checked.Fidelity.HubbleSpec hubbleOff where
  logDeriv a t ha hd := by
    rw [hubbleOff, ite_eq_left ⟨ha, hd⟩]; exact Checked.Fidelity.hubble_meets_spec.logDeriv a t ha hd
  deSitter h t := by
    rw [hubbleOff, ite_eq_left ⟨Real.exp_pos _, by fun_prop⟩]
    exact Checked.Fidelity.hubble_meets_spec.deSitter h t
  powerLaw n t ht := by
    rw [hubbleOff, ite_eq_left ⟨Real.rpow_pos_of_pos ht n,
      (Real.hasDerivAt_rpow_const (Or.inl ht.ne')).differentiableAt⟩]
    exact Checked.Fidelity.hubble_meets_spec.powerLaw n t ht
  static R t hR := by
    rw [hubbleOff, ite_eq_left ⟨hR, differentiableAt_const _⟩]
    exact Checked.Fidelity.hubble_meets_spec.static R t hR
  rescale c hc a t ha hd := by
    rw [hubbleOff, hubbleOff, ite_eq_left ⟨mul_pos hc ha, hd.const_mul c⟩, ite_eq_left ⟨ha, hd⟩]
    exact Checked.Fidelity.hubble_meets_spec.rescale c hc a t ha hd
  translate τ a t ha hd := by
    have hd' : DifferentiableAt ℝ (fun s => a (s + τ)) t :=
      hd.comp t (differentiableAt_id.add_const τ)
    rw [hubbleOff, hubbleOff, ite_eq_left ⟨ha, hd'⟩, ite_eq_left ⟨ha, hd⟩]
    exact Checked.Fidelity.hubble_meets_spec.translate τ a t ha hd
  timeReverse a t ha hd := by
    have hd' : DifferentiableAt ℝ (fun s => a (-s)) t := hd.comp t differentiableAt_id.neg
    rw [hubbleOff, hubbleOff, ite_eq_left ⟨ha, hd'⟩, ite_eq_left ⟨ha, hd⟩]
    exact Checked.Fidelity.hubble_meets_spec.timeReverse a t ha hd

theorem hubbleSpec_pins_h2 : necessity% Checked.Fidelity.hubbleSpec_pins 2 := by
  refine ⟨hubbleOff, hubbleOff_spec, fun s => -Real.exp s, 0, by fun_prop, ?_⟩
  have : ¬ (0 < (fun s => -Real.exp s) 0 ∧ DifferentiableAt ℝ (fun s => -Real.exp s) 0) :=
    fun h => absurd h.1 (by simp)
  rw [hubbleOff, ite_eq_right this]; norm_num

theorem hubbleSpec_pins_h3 : necessity% Checked.Fidelity.hubbleSpec_pins 3 := by
  refine ⟨hubbleOff, hubbleOff_spec, fun s => 1 + |s|, 0, by positivity, ?_⟩
  have hnd : ¬ DifferentiableAt ℝ (fun s : ℝ => 1 + |s|) 0 := by
    intro h
    have := (h.const_add (-1)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by ring)
    exact not_differentiableAt_abs_zero this
  rw [hubbleOff, ite_eq_right (fun h => hnd h.2)]; norm_num

/- `YRedSpec` constrains its function only where the scale factor is positive at both times; `yred` shifted by
one elsewhere meets it and differs from `yred` when either value is negative (`a = −t` or `a = t`). -/

open Classical in
noncomputable def yredOff (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  if 0 < a t₀ ∧ 0 < a t then yred a t₀ t else yred a t₀ t + 1

theorem yredOff_eq {a : ℝ → ℝ} {t₀ t : ℝ} (h0 : 0 < a t₀) (h1 : 0 < a t) :
    yredOff a t₀ t = yred a t₀ t := by
  rw [yredOff, ite_eq_left ⟨h0, h1⟩]

theorem yredOff_spec : Checked.Fidelity.YRedSpec yredOff := by
  have M := Checked.Fidelity.yred_meets_spec
  have m1 : ∀ s : ℝ, 0 < s → 0 < (fun s : ℝ => s) s := fun s h => h
  refine ⟨fun a t₀ t h0 h1 => ?_, fun a t₀ t h0 h1 => ?_, fun a t₀ t h0 h1 => ?_,
    fun a t₀ t h0 h1 => ?_, fun a t₀ t h0 h1 => ?_, fun a b t₀ t h0 h1 hb hab hlt => ?_,
    fun a t₀ h => ?_, fun H t₀ t => ?_, fun t₀ t h₀ h => ?_, ?_, fun c t₀ t hc => ?_,
    fun c a t₀ t hc h0 h1 => ?_, fun τ a t₀ t h0 h1 => ?_, fun a b t₀ t h0 h1 h2 h3 => ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [yredOff_eq h0 h1]; exact M.law a t₀ t h0 h1
  · rw [yredOff_eq h0 h1]; exact M.of_z a t₀ t h0 h1
  · rw [yredOff_eq h0 h1]; exact M.inv_z a t₀ t h0 h1
  · rw [yredOff_eq h0 h1]; exact M.lt_one a t₀ t h0 h1
  · rw [yredOff_eq h0 h1]; exact M.pos_iff a t₀ t h0 h1
  · rw [yredOff_eq h0 h1, yredOff_eq (hab ▸ h0) hb]; exact M.strictAnti_a a b t₀ t h0 h1 hb hab hlt
  · rw [yredOff_eq h h]; exact M.self a t₀ h
  · rw [yredOff_eq (a := fun s => Real.exp (H * s)) (Real.exp_pos _) (Real.exp_pos _)]
    exact M.deSitter H t₀ t
  · rw [yredOff_eq (m1 t₀ h₀) (m1 t h)]; exact M.milne t₀ t h₀ h
  · rw [yredOff_eq (m1 2 (by norm_num)) (m1 1 (by norm_num))]; exact M.milne_value
  · rw [yredOff_eq hc hc]; exact M.static c t₀ t hc
  · rw [yredOff_eq (a := fun s => c * a s) (mul_pos hc h0) (mul_pos hc h1), yredOff_eq h0 h1]
    exact M.scale_inv c a t₀ t hc h0 h1
  · rw [yredOff_eq (a := fun s => a (s + τ)) (by simpa using h0) (by simpa using h1),
      yredOff_eq h0 h1]
    exact M.shift_inv τ a t₀ t h0 h1
  · rw [yredOff_eq h0 h1, yredOff_eq (h2 ▸ h0) (h3 ▸ h1)]; exact M.local_values a b t₀ t h0 h1 h2 h3
  · rw [yredOff_eq (m1 3 (by norm_num)) (m1 1 (by norm_num))]; exact M.not_z_div_one_sub_z
  · rw [yredOff_eq (m1 2 (by norm_num)) (m1 1 (by norm_num))]; exact M.not_z
  · rw [yredOff_eq (m1 2 (by norm_num)) (m1 1 (by norm_num))]; exact M.not_neg
  · rw [yredOff_eq (m1 2 (by norm_num)) (m1 1 (by norm_num))]; exact M.not_neg_z
  · rw [yredOff_eq (m1 2 (by norm_num)) (m1 1 (by norm_num))]; exact M.not_log

theorem yRedSpec_pins_h2 : necessity% Checked.Fidelity.yRedSpec_pins 2 := by
  refine ⟨yredOff, yredOff_spec, fun s => -s, 1, -1, by norm_num, ?_⟩
  rw [yredOff, ite_eq_right (fun h => absurd h.1 (by norm_num))]; norm_num

theorem yRedSpec_pins_h3 : necessity% Checked.Fidelity.yRedSpec_pins 3 := by
  refine ⟨yredOff, yredOff_spec, fun s => s, 1, -1, by norm_num, ?_⟩
  rw [yredOff, ite_eq_right (fun h => absurd h.2 (by norm_num))]; norm_num

/- `Omega0Spec` constrains its function only where `a t₀ > 0`, `a` is differentiable at `t₀` and the Hubble
rate is nonzero; `omega0` shifted by one elsewhere meets it. Positivity and a nonzero Hubble rate are NEEDED
(`a = −exp`; the static model); differentiability is REDUNDANT (a nonzero Hubble rate needs a nonzero, hence
genuine, derivative), also in `curvKSpec_pins`. -/

def OmOK (a : ℝ → ℝ) (t₀ : ℝ) : Prop :=
  0 < a t₀ ∧ DifferentiableAt ℝ a t₀ ∧ deriv a t₀ / a t₀ ≠ 0

open Classical in
noncomputable def omega0Off (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) : ℝ :=
  if OmOK a t₀ then omega0 K a t₀ else omega0 K a t₀ + 1

theorem omega0Off_eq {K : ℝ} {a : ℝ → ℝ} {t₀ : ℝ} (h : OmOK a t₀) :
    omega0Off K a t₀ = omega0 K a t₀ := by
  rw [omega0Off, ite_eq_left h]

theorem omOK_id (t : ℝ) (ht : 0 < t) : OmOK (fun s : ℝ => s) t :=
  ⟨ht, differentiableAt_id, by rw [Checked.Fidelity.hubble_id']; exact one_div_ne_zero ht.ne'⟩

theorem omega0Off_spec : Checked.Fidelity.Omega0Spec omega0Off := by
  have M := Checked.Fidelity.omega0_meets_spec
  refine ⟨fun K a t₀ ha hd hH => ?_, fun G ρ K a t₀ hG ha hd hH hF => ?_, fun a t₀ ha hd hH => ?_,
    fun t₀ h => ?_, fun t₀ h => ?_, ?_, fun K a t₀ ha hd hH => ?_, fun K a t₀ ha hd hH => ?_,
    fun c K a t₀ hc ha hd hH => ?_, fun τ K a t₀ ha hd hH => ?_, fun K a b t₀ ha hd hH h => ?_,
    ?_, ?_⟩
  · rw [omega0Off_eq ⟨ha, hd, hH⟩]; exact M.law K a t₀ ha hd hH
  · rw [omega0Off_eq ⟨ha, hd, hH⟩]; exact M.friedmann G ρ K a t₀ hG ha hd hH hF
  · rw [omega0Off_eq ⟨ha, hd, hH⟩]; exact M.flat a t₀ ha hd hH
  · rw [omega0Off_eq (omOK_id t₀ h)]; exact M.milne t₀ h
  · have hs : Real.sinh t₀ ≠ 0 := by rwa [ne_eq, Real.sinh_eq_zero]
    rw [omega0Off_eq ⟨Real.cosh_pos t₀, Real.differentiable_cosh t₀,
      by rw [Real.deriv_cosh]; exact div_ne_zero hs (Real.cosh_pos t₀).ne'⟩]
    exact M.closed_deSitter t₀ h
  · rw [omega0Off_eq (omOK_id 1 one_pos)]; exact M.closed_value
  · rw [omega0Off_eq ⟨ha, hd, hH⟩]; exact M.gt_one_iff K a t₀ ha hd hH
  · rw [omega0Off_eq ⟨ha, hd, hH⟩]; exact M.lt_one_iff K a t₀ ha hd hH
  · have hok : OmOK (fun s => c * a s) t₀ := by
      refine ⟨mul_pos hc ha, hd.const_mul c, ?_⟩
      rw [deriv_const_mul_field', mul_div_mul_left _ _ hc.ne']; exact hH
    rw [omega0Off_eq hok, omega0Off_eq ⟨ha, hd, hH⟩]; exact M.rescale c K a t₀ hc ha hd hH
  · have hok : OmOK (fun s => a (s + τ)) (t₀ - τ) := by
      refine ⟨by simpa using ha, ?_, ?_⟩
      · have : DifferentiableAt ℝ a ((t₀ - τ) + τ) := by simpa using hd
        exact this.comp (t₀ - τ) (differentiableAt_id.add_const τ)
      · rw [deriv_comp_add_const, sub_add_cancel]; simpa using hH
    rw [omega0Off_eq hok, omega0Off_eq ⟨ha, hd, hH⟩]; exact M.shift_inv τ K a t₀ ha hd hH
  · have hok : OmOK b t₀ := by
      refine ⟨h.eq_of_nhds ▸ ha, hd.congr_of_eventuallyEq h.symm, ?_⟩
      rw [← h.deriv_eq, ← h.eq_of_nhds]; exact hH
    rw [omega0Off_eq hok, omega0Off_eq ⟨ha, hd, hH⟩]; exact M.local_germ K a b t₀ ha hd hH h
  · rw [omega0Off_eq (omOK_id 1 one_pos)]; exact M.not_sign_flip
  · have hok : OmOK (fun s : ℝ => 2 * s) 1 :=
      ⟨by norm_num, by fun_prop, by rw [Checked.Fidelity.deriv_two_mul]; norm_num⟩
    rw [omega0Off_eq hok]
    exact M.not_missing_a0

theorem omega0Spec_pins_h2 : necessity% Checked.Fidelity.omega0Spec_pins 2 := by
  refine ⟨omega0Off, omega0Off_spec, 0, fun s => -Real.exp s, 0, by fun_prop,
    by simp [Real.deriv_exp], ?_⟩
  rw [omega0Off, ite_eq_right (fun h => absurd h.1 (by simp))]; norm_num

theorem omega0Spec_pins_r3 : dropped% Checked.Fidelity.omega0Spec_pins 3 := by
  intro O h K a t₀ ha hH
  have hd : DifferentiableAt ℝ a t₀ :=
    differentiableAt_of_deriv_ne_zero (fun h0 => hH (by rw [h0, zero_div]))
  exact Checked.Fidelity.omega0Spec_pins O h K a t₀ ha hd hH

theorem omega0Spec_pins_h4 : necessity% Checked.Fidelity.omega0Spec_pins 4 := by
  refine ⟨omega0Off, omega0Off_spec, 0, fun _ => 1, 0, one_pos, differentiableAt_const _, ?_⟩
  rw [omega0Off, ite_eq_right (fun h => h.2.2 (by simp))]; norm_num

theorem curvKSpec_pins_r3 : dropped% Checked.Fidelity.curvKSpec_pins 3 := by
  intro k h K a t₀ ha hH
  have hd : DifferentiableAt ℝ a t₀ :=
    differentiableAt_of_deriv_ne_zero (fun h0 => hH (by rw [h0, zero_div]))
  exact Checked.Fidelity.curvKSpec_pins k h K a t₀ ha hd hH

open Classical in
noncomputable def curvKOff (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) : ℝ :=
  if OmOK a t₀ then curvK K a t₀ else curvK K a t₀ + 1

theorem curvKOff_eq {K : ℝ} {a : ℝ → ℝ} {t₀ : ℝ} (h : OmOK a t₀) :
    curvKOff K a t₀ = curvK K a t₀ := by
  rw [curvKOff, ite_eq_left h]

theorem curvKOff_spec : Checked.Fidelity.CurvKSpec curvKOff := by
  have M := Checked.Fidelity.curvK_meets_spec
  have h2 : OmOK (fun s : ℝ => 2 * s) 1 :=
    ⟨by norm_num, by fun_prop, by rw [Checked.Fidelity.deriv_two_mul]; norm_num⟩
  refine ⟨fun K a t₀ ha hd hH => ?_, fun K a t₀ ha hd hd' => ?_,
    fun G ρ K a t₀ hG ha hd hH hF => ?_, fun a t₀ ha hd hH => ?_, fun t₀ h => ?_, fun t₀ h => ?_,
    fun K a t₀ ha hd hH => ?_, fun K a t₀ ha hd hH => ?_, fun r K a t₀ ha hd hH => ?_,
    fun c K a t₀ hc ha hd hH => ?_, fun τ K a t₀ ha hd hH => ?_, ?_, ?_, ?_⟩
  · rw [curvKOff_eq ⟨ha, hd, hH⟩]; exact M.law K a t₀ ha hd hH
  · rw [curvKOff_eq ⟨ha, hd, div_ne_zero hd' ha.ne'⟩]; exact M.law_adot K a t₀ ha hd hd'
  · rw [curvKOff_eq ⟨ha, hd, hH⟩]; exact M.friedmann G ρ K a t₀ hG ha hd hH hF
  · rw [curvKOff_eq ⟨ha, hd, hH⟩]; exact M.flat a t₀ ha hd hH
  · rw [curvKOff_eq (omOK_id t₀ h)]; exact M.milne t₀ h
  · have hs : Real.sinh t₀ ≠ 0 := by rwa [ne_eq, Real.sinh_eq_zero]
    rw [curvKOff_eq ⟨Real.cosh_pos t₀, Real.differentiable_cosh t₀,
      by rw [Real.deriv_cosh]; exact div_ne_zero hs (Real.cosh_pos t₀).ne'⟩]
    exact M.closed_deSitter t₀ h
  · rw [curvKOff_eq ⟨ha, hd, hH⟩]; exact M.pos_iff K a t₀ ha hd hH
  · rw [curvKOff_eq ⟨ha, hd, hH⟩]; exact M.neg_iff K a t₀ ha hd hH
  · rw [curvKOff_eq ⟨ha, hd, hH⟩, curvKOff_eq ⟨ha, hd, hH⟩]; exact M.linear_K r K a t₀ ha hd hH
  · have hok : OmOK (fun s => c * a s) t₀ := by
      refine ⟨mul_pos hc ha, hd.const_mul c, ?_⟩
      rw [deriv_const_mul_field', mul_div_mul_left _ _ hc.ne']; exact hH
    rw [curvKOff_eq hok, curvKOff_eq ⟨ha, hd, hH⟩]; exact M.rescale c K a t₀ hc ha hd hH
  · have hok : OmOK (fun s => a (s + τ)) (t₀ - τ) := by
      refine ⟨by simpa using ha, ?_, ?_⟩
      · have : DifferentiableAt ℝ a ((t₀ - τ) + τ) := by simpa using hd
        exact this.comp (t₀ - τ) (differentiableAt_id.add_const τ)
      · rw [deriv_comp_add_const, sub_add_cancel]; simpa using hH
    rw [curvKOff_eq hok, curvKOff_eq ⟨ha, hd, hH⟩]; exact M.shift_inv τ K a t₀ ha hd hH
  · rw [curvKOff_eq (omOK_id 1 one_pos)]; exact M.not_omega_k
  · rw [curvKOff_eq h2]; exact M.not_missing_a0
  · rw [curvKOff_eq h2]; exact M.value_2t

theorem curvKSpec_pins_h2 : necessity% Checked.Fidelity.curvKSpec_pins 2 := by
  refine ⟨curvKOff, curvKOff_spec, 1, fun s => -Real.exp s, 0, by fun_prop,
    by simp [Real.deriv_exp], ?_⟩
  rw [curvKOff, ite_eq_right (fun h => absurd h.1 (by simp))]; norm_num

theorem curvKSpec_pins_h4 : necessity% Checked.Fidelity.curvKSpec_pins 4 := by
  refine ⟨curvKOff, curvKOff_spec, 1, fun _ => 1, 0, one_pos, differentiableAt_const _, ?_⟩
  rw [curvKOff, ite_eq_right (fun h => h.2.2 (by simp))]; norm_num

/- `DecelSpec` constrains its function only where `a t > 0` and `ȧ ≠ 0` (its invariance fields preserve both);
`decel` shifted by one elsewhere meets it, so positivity and `ȧ ≠ 0` are NEEDED in `decelSpec_pins`
(`a = −exp`; `a = 1 + t²` at `0`). -/

open Classical in
noncomputable def decelOff (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  if 0 < a t ∧ deriv a t ≠ 0 then decel a t else decel a t + 1

theorem rpow_deriv_ne (n t : ℝ) (hn : n ≠ 0) (ht : 0 < t) : deriv (fun s : ℝ => s ^ n) t ≠ 0 := by
  rw [(Real.hasDerivAt_rpow_const (Or.inl ht.ne')).deriv]
  exact mul_ne_zero hn (Real.rpow_pos_of_pos ht _).ne'

theorem decelOff_spec : Checked.Fidelity.DecelSpec decelOff := by
  have M := Checked.Fidelity.decel_meets_spec
  refine ⟨fun a a' a'' t h1 h2 ha hd => ?_, fun h t hh => ?_, fun n t hn ht => ?_, fun t ht => ?_,
    fun n t hn ht => ?_, fun c hc a t hd => ?_, fun τ a t hd => ?_, fun a t hd => ?_⟩
  · have hd' : deriv a t ≠ 0 := by
      rw [(h1.self_of_nhds).deriv]; exact hd
    rw [decelOff, ite_eq_left ⟨ha, hd'⟩]; exact M.formula a a' a'' t h1 h2 ha hd
  · have hD : deriv (fun s => Real.exp (h * s)) t ≠ 0 := by
      rw [(Checked.Fidelity.ms_hasDerivAt_expMul h t).deriv]
      exact mul_ne_zero hh (Real.exp_pos _).ne'
    rw [decelOff, ite_eq_left ⟨Real.exp_pos _, hD⟩]; exact M.deSitter h t hh
  · rw [decelOff, ite_eq_left ⟨Real.rpow_pos_of_pos ht n, rpow_deriv_ne n t hn ht⟩]
    exact M.powerLaw n t hn ht
  · rw [decelOff, ite_eq_left ⟨Real.rpow_pos_of_pos ht _, rpow_deriv_ne _ t (by norm_num) ht⟩]
    exact M.eds t ht
  · have hD : deriv (fun s : ℝ => (-s) ^ n) t ≠ 0 := by
      have e := deriv_comp_neg (fun s : ℝ => s ^ n) t
      rw [e]
      exact neg_ne_zero.2 (rpow_deriv_ne n (-t) hn (by linarith))
    rw [decelOff, ite_eq_left ⟨Real.rpow_pos_of_pos (by linarith) n, hD⟩]
    exact M.crunch n t hn ht
  · have e : deriv (fun s => c * a s) t = c * deriv a t := by rw [deriv_const_mul_field']
    have hiff : (0 < c * a t ∧ deriv (fun s => c * a s) t ≠ 0) ↔ (0 < a t ∧ deriv a t ≠ 0) := by
      rw [e, mul_pos_iff_of_pos_left hc, mul_ne_zero_iff, and_iff_right hc.ne']
    have hM := M.rescale c hc a t hd
    unfold decelOff
    by_cases h : 0 < a t ∧ deriv a t ≠ 0
    · rw [ite_eq_left h, ite_eq_left (hiff.2 h), hM]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.1 h')), hM]
  · have e : deriv (fun s => a (s + τ)) t = deriv a (t + τ) := deriv_comp_add_const a τ t
    have hM := M.translate τ a t hd
    unfold decelOff
    simp only [e]
    by_cases h : 0 < a (t + τ) ∧ deriv a (t + τ) ≠ 0
    · rw [ite_eq_left h, ite_eq_left h, hM]
    · rw [ite_eq_right h, ite_eq_right h, hM]
  · have e : deriv (fun s => a (-s)) t = -deriv a (-t) := deriv_comp_neg a t
    have hM := M.timeReverse a t hd
    unfold decelOff
    have hiff : (0 < a (-t) ∧ -deriv a (-t) ≠ 0) ↔ (0 < a (-t) ∧ deriv a (-t) ≠ 0) := by
      rw [neg_ne_zero]
    simp only [e]
    by_cases h : 0 < a (-t) ∧ deriv a (-t) ≠ 0
    · rw [ite_eq_left (hiff.2 h), ite_eq_left h, hM]
    · rw [ite_eq_right (fun h' => h (hiff.1 h')), ite_eq_right h, hM]

theorem decelSpec_pins_h4 : necessity% Checked.Fidelity.decelSpec_pins 4 := by
  refine ⟨decelOff, decelOff_spec, fun s => -Real.exp s, fun s => -Real.exp s, -Real.exp 0, 0,
    Filter.Eventually.of_forall fun s => (Real.hasDerivAt_exp s).neg, (Real.hasDerivAt_exp 0).neg,
    by simp, ?_⟩
  rw [decelOff, ite_eq_right (fun h => absurd h.1 (by simp))]; norm_num

theorem decelSpec_pins_h5 : necessity% Checked.Fidelity.decelSpec_pins 5 := by
  have hD : ∀ s : ℝ, HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * s) s := fun s => by
    simpa using ((hasDerivAt_pow 2 s).const_add 1)
  have hD2 : HasDerivAt (fun s : ℝ => 2 * s) 2 0 := by simpa using (hasDerivAt_id (0:ℝ)).const_mul 2
  refine ⟨decelOff, decelOff_spec, fun s => 1 + s ^ 2, fun s => 2 * s, 2, 0,
    Filter.Eventually.of_forall hD, hD2, by norm_num, ?_⟩
  rw [decelOff, ite_eq_right (fun h => h.2 (by rw [(hD 0).deriv]; norm_num))]; norm_num

end Pins

end Checked.Trust.NCL
