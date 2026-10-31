import Checked.Records.Basic
import Checked.Cosmography.LCDMWitness
import Checked.Cosmography.CPLExistence
import Checked.Cosmography.CCSLookback
import Checked.Cosmography.FREta

/-!
# Certified numbers of the verified findings F1–F11 (run 2026-10-31T0228Z)

Every computed decimal in `FINDINGS.md` ("Verified findings") is tagged `[✓name]`; `name` is a
theorem below whose statement contains `RoundsTo x d k` with the decimal `d` shown in the prose
(checked by `scripts/trust/check_numbers.py` in CI). Where the number is a physical quantity the
statement quantifies over *every model* (pinned definitions `IsFlatLCDM`, `IsFlatCPL`,
`cosmoCoeff`, `decel`); where it is the value of a printed or derived formula the formula is
written out (or is a FORMULA/PRINTED definition) so the reader sees what was evaluated.
Parameters are written as exact fractions (0.3 = 3/10, 0.041 = 41/1000).
-/

namespace Checked.Records

open Checked.Cosmography Checked.Cosmography.Aviles

/-! ## F1 (Aviles et al. 2012, Eq. (15)) -/

/-- In every flat ΛCDM model with `Ω_m = 0.3`, `l₀ = 3.115` (to 3 decimals). -/
theorem F1_l0 (a : ℝ → ℝ) (t₀ : ℝ) (hL : IsFlatLCDM (3 / 10) a t₀)
    (hs : ContDiffAt ℝ 6 a t₀) : RoundsTo (cosmoCoeff 5 a t₀) 3.115 3 := by
  rw [(flatLCDM_coeffs _ a t₀ hL hs).2.2.2.1]
  unfold RoundsTo; rw [abs_le]; norm_num

/-- The printed `l₀ = 1 + 3Ω − (27/2)Ω²` at `Ω = 0.3` is `0.685`. -/
theorem F1_printedL0 : RoundsTo (1 + 3 * (3 / 10) - 27 / 2 * (3 / 10) ^ 2) 0.685 3 := by
  unfold RoundsTo; rw [abs_le]; norm_num

/-- There is a matter fraction `Ω ≈ 0.549` in `(0, 1)` at which the printed `m₀` agrees with the
true `m₀` of every flat ΛCDM model (`Ω = (√7 − 1)/3`). -/
theorem F1_m0_agrees : ∃ r : ℝ, RoundsTo r 0.549 3 ∧ 0 < r ∧ r < 1 ∧
    ∀ (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM r a t₀ → ContDiffAt ℝ 6 a t₀ →
      cosmoCoeff 6 a t₀ = 1 - 27 / 2 * r ^ 2 - 81 * r ^ 2 - 81 / 2 * r ^ 3 := by
  have h7 : √7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have h0 : 0 ≤ √7 := Real.sqrt_nonneg 7
  have hlo : 2.6457 ≤ √7 := by nlinarith
  have hhi : √7 ≤ 2.6458 := by nlinarith
  refine ⟨(√7 - 1) / 3, ?_, by linarith, by linarith, fun a t₀ hL hs => ?_⟩
  · unfold RoundsTo; rw [abs_le]; constructor <;> norm_num <;> linarith
  · rw [(flatLCDM_coeffs _ a t₀ hL hs).2.2.2.2]
    have hr : 3 * ((√7 - 1) / 3) ^ 2 + 2 * ((√7 - 1) / 3) - 2 = 0 := by nlinarith
    linear_combination (27 / 4 * ((√7 - 1) / 3)) * hr

/-! ## F2 (Capozziello, Lazkoz, Salzano 2011, Eq. (22)) -/

/-- The printed CPL `l₀` (Eq. (22)), written out. -/
local notation "printedCPLl0" Ω:max w₀:max wₐ:max =>
  35 / 2 + (1 - Ω) / 4 * (213 + (7 - Ω) * wₐ) * wₐ
      + (1 - Ω) / 4 * (489 + 9 * (82 - 21 * Ω) * wₐ) * w₀
      + 9 / 2 * (1 - Ω) * (67 - 21 * Ω + 3 / 2 * (23 - 11 * Ω) * wₐ) * w₀ ^ 2
      + 27 / 4 * (1 - Ω) * (47 - 24 * Ω) * w₀ ^ 3
      + 81 / 2 * (1 - Ω) * (3 - 2 * Ω) * w₀ ^ 4

/-- The paper's toy model `(Ω, w₀, wₐ) = (0.245, −0.93, −0.41)`: in every flat matter + CPL model
with these parameters `l₀ = 0.809`, while the printed formula gives `−0.906`. -/
theorem F2_toy (a : ℝ → ℝ) (t₀ : ℝ)
    (hL : CPL.IsFlatCPL (245 / 1000) (-93 / 100) (-41 / 100) a t₀)
    (hs : ContDiffAt ℝ 5 a t₀) :
    RoundsTo (cosmoCoeff 5 a t₀) 0.809 3 ∧
      RoundsTo (printedCPLl0 (245 / 1000 : ℝ) (-93 / 100 : ℝ) (-41 / 100 : ℝ)) (-0.906) 3 := by
  rw [(CPL.flatCPL_coeffs _ _ _ a t₀ hL hs).2.2.2]
  unfold RoundsTo; simp only [abs_le]; norm_num

/-- At `Ω = 0.3`, `wₐ = −0.5` and every `w₀`, every flat CPL model has `l₀` exceeding the printed
formula by `2.345`. -/
theorem F2_error (w₀ : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (hL : CPL.IsFlatCPL (3 / 10) w₀ (-1 / 2) a t₀)
    (hs : ContDiffAt ℝ 5 a t₀) :
    RoundsTo (cosmoCoeff 5 a t₀ - printedCPLl0 (3 / 10 : ℝ) w₀ (-1 / 2 : ℝ)) 2.345 3 := by
  rw [(CPL.flatCPL_coeffs _ _ _ a t₀ hL hs).2.2.2]
  have : ∀ x : ℝ, x = 2.345 → |x - 2.345| ≤ 1 / (2 * 10 ^ 3) := fun x hx => by
    rw [hx]; norm_num
  exact this _ (by ring)

/-! ## F3 (Capozziello, Cardone, Salzano 2008, Eq. (A2)) -/

/-- In every flat ΛCDM model with `Ω_m = 0.3` (q₀ = −0.55): the correct lookback `D⁴` is
`0.2153`, the printed one `0.4555`, and the excess `printed − correct` is `0.24`. -/
theorem F3_D4_LCDM (a : ℝ → ℝ) (t₀ : ℝ) (hL : IsFlatLCDM (3 / 10) a t₀)
    (hs : ContDiffAt ℝ 6 a t₀) :
    RoundsTo (CCS.correctD4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀)
      (cosmoCoeff 5 a t₀)) 0.2153 4 ∧
    RoundsTo (CCS.printedD4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀)
      (cosmoCoeff 5 a t₀)) 0.4555 4 ∧
    RoundsTo (CCS.printedD4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀)
      (cosmoCoeff 5 a t₀) - CCS.correctD4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀)
      (cosmoCoeff 5 a t₀)) 0.24 2 := by
  obtain ⟨hq, hj, hs4, hl, -⟩ := flatLCDM_coeffs _ a t₀ hL hs
  rw [hq, hj, hs4, hl]
  unfold CCS.correctD4 CCS.printedD4 RoundsTo; simp only [abs_le]; norm_num

/-! ## F8 (Bamba et al. 2012, (10.38)–(10.51)) -/

/-- Size of the omitted `k²z⁴/120`: for `|k| = 0.01` at `z = 2` it is `1.3 × 10⁻⁵`. In Milne
(`H₀d_L = z + z²/2` exactly) the omitted `z⁵/120` relative to `H₀d_L` is `0.56 %` at `z = 1` and
`6.7 %` at `z = 2`. -/
theorem F8_sizes :
    RoundsTo ((1 / 100) ^ 2 * 2 ^ 4 / 120) 0.000013 6 ∧
    RoundsTo (100 * ((1 : ℝ) ^ 5 / 120) / (1 + 1 ^ 2 / 2)) 0.56 2 ∧
    RoundsTo (100 * ((2 : ℝ) ^ 5 / 120) / (2 + 2 ^ 2 / 2)) 6.7 1 := by
  unfold RoundsTo; simp only [abs_le]; norm_num

/-! ## F9 (Bamba et al. 2012, (11.21) with the printed R) -/

/-- At `Ω = 0.25` the printed (11.21) gives `F(R₀) = 0.277 H₀²`; the ΛCDM value `3H₀²(Ω − 2)` is
`−5.25 H₀²` (`H₀ = 1`). -/
theorem F9_values :
    RoundsTo (27 * (1 / 4) ^ 2 * ((1 / 4) - 2) * (27 * (1 / 4) ^ 2 + 60 * (1 / 4) + 112) /
      (243 * (1 / 4) ^ 4 + 540 * (1 / 4) ^ 3 - 6264 * (1 / 4) ^ 2 + 9360 * (1 / 4) - 3328)) 0.277 3 ∧
    RoundsTo (3 * ((1 / 4 : ℝ) - 2)) (-5.25) 2 := by
  unfold RoundsTo; simp only [abs_le]; norm_num

/-- The denominator of the printed (11.21) in ΛCDM vanishes at some `Ω ≈ 0.538`. -/
theorem F9_pole : ∃ r : ℝ, RoundsTo r 0.538 3 ∧
    243 * r ^ 4 + 540 * r ^ 3 - 6264 * r ^ 2 + 9360 * r - 3328 = 0 :=
  exists_root_roundsTo (by fun_prop) _ _ (by norm_num)

/-! ## F10 (Bamba et al. 2012, (11.42)–(11.45)) -/

/-- The correct first-order coefficients (`FREta.correct20`, `correct30`, the `ε`-derivatives of
η₂₀, η₃₀ by `FREta.eta20_hasDerivAt`, `eta30_hasDerivAt`) at the paper's `Ω = 0.041, 0.25`. -/
theorem F10_eta :
    RoundsTo (FREta.correct20 (41 / 1000)) (-0.249) 3 ∧
    RoundsTo (FREta.correct20 (1 / 4)) (-0.032) 3 ∧
    RoundsTo (FREta.correct30 (41 / 1000)) (-0.400) 3 ∧
    RoundsTo (FREta.correct30 (1 / 4)) (-0.0152) 4 := by
  unfold FREta.correct20 FREta.correct30 RoundsTo; simp only [abs_le]; norm_num

/-- The printed denominator (11.42)–(11.43) vanishes at some `Ω ≈ 0.176` (spurious pole). -/
theorem F10_printed_pole : ∃ r : ℝ, RoundsTo r 0.176 3 ∧ FREta.printedDen r = 0 := by
  unfold FREta.printedDen
  exact exists_root_roundsTo (by fun_prop) _ _ (by norm_num)

/-- The only points of `(0, 1)` not covered by `printedEta20_false_at`, `printedEta30_false_at`
(their hypothesis `(54Ω² − 29Ω − 2)(27Ω² + 24Ω − 32) ≠ 0`) are `Ω ≈ 0.599` and `Ω ≈ 0.731`. -/
theorem F10_exceptions :
    (∃ r : ℝ, RoundsTo r 0.599 3 ∧ 54 * r ^ 2 - 29 * r - 2 = 0) ∧
    (∃ r : ℝ, RoundsTo r 0.731 3 ∧ 27 * r ^ 2 + 24 * r - 32 = 0) :=
  ⟨exists_root_roundsTo (by fun_prop) _ _ (by norm_num),
    exists_root_roundsTo (by fun_prop) _ _ (by norm_num)⟩

/-- At `Ω = 0.041` the ε-family (11.41) reaches `j₀ − q₀ − 2 = 0` at `ε ≈ 0.032`. -/
theorem F10_family_pole : ∃ ε : ℝ, RoundsTo ε 0.032 3 ∧ FREta.Jfam (41 / 1000) ε = 0 := by
  refine ⟨123 / 3877, ?_, ?_⟩
  · unfold RoundsTo; simp only [abs_le]; norm_num
  · unfold FREta.Jfam FREta.jL FREta.qL; norm_num

/-! ## F11 (Demianski et al. 2017; Lusso et al. 2019) -/

/-- At `q₀ = −0.80`: the shift `l₀ ↦ l₀ − 210q₀⁴` that absorbs the D⁴_L error is `−86`, and the
error `(7/4)q₀⁴ z⁴` inside the bracket at `z = 1` is `0.72`. -/
theorem F11_sizes :
    RoundsTo (-210 * (-4 / 5) ^ 4) (-86) 0 ∧ RoundsTo (7 / 4 * (-4 / 5) ^ 4) 0.72 2 := by
  unfold RoundsTo; simp only [abs_le]; norm_num

end Checked.Records
