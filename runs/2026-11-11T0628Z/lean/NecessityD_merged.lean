import Checked.Trust.NonVacuity
import Checked.Cosmography.CCSLookback
import Checked.Cosmography.BambaDLy
import Checked.Cosmography.CVdQ
import Checked.Cosmography.BambaCurved
import Checked.Cosmography.BambaAngular
import Checked.Cosmography.BambaZ
import Checked.Cosmography.DemianskiZ
import Checked.Cosmography.LookbackThird
import Mathlib.Analysis.Calculus.Deriv.Abs
import Checked.Records.Findings
import Checked.Cosmography.CPLExistence
import Checked.Chemistry.CubicEOS
import Checked.Cosmography.LCDMWitness
import Checked.FalknerSkan.Separation
import Checked.FalknerSkan.SeparationEqual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Hypothesis necessity witnesses, fourth batch (trust track T2b, run 2026-11-11T0628Z; scratch `runs/2026-11-11T0628Z/lean/`)

The cosmographic "printed coefficient fails" headlines (`CCS.printedD4_fails`, `BambaY.printedD2y_fails`,
`CVdQ.printedQ2_fails_past`, `BambaK.printedD3y_fails`, `BambaK.printedD4y_fails`, `BambaA.printedDA3_fails`,
`BambaA.printedDA4_fails`, `BambaZ.printedDL4z_fails_past`, `BambaZ.printedDA4z_fails_past`,
`DemianskiZ.demDL4_fails_past`, `DemianskiZ.demDA4_fails_past`, and their past-only or two-sided
companions) have four hypotheses: smoothness, `a(t₀) ≠ 0`, `H₀ ≠ 0`, and a condition saying the
printed coefficient differs from the correct one. This file classifies the last two.

* **The printed-coefficient condition (hypothesis 4) is needed** in every one of them: a model in which
  the condition is zero makes the printed coefficient equal to the correct one, and the correct-order
  series theorem then gives the very remainder bound the headline denies. The models are
  `a = 1 + t + c t³` at `t₀ = 0` (`H₀ = 1`, `q₀ = 0`, `j₀ = 6c`) and, for the curvature conditions,
  zero curvature `K = 0` (`Ω₀ = 1`).
* **A nonzero Hubble rate (hypothesis 3) is needed** where the printed-coefficient condition does not
  mention `q₀`, `j₀` or `Ω₀ − 1` (`BambaY.printedD2y_fails_past`, `CVdQ.printedQ2_fails_past`,
  `BambaZ.printedDL4z_fails_past`, `BambaZ.printedDA4z_fails_past`): in a static model `a = 1` the
  redshift is zero, `H₀` is zero, the remainder vanishes identically and is `o` of anything.
* **It is redundant** where the condition does mention them (`CCS`, `BambaK`, `BambaA`, `DemianskiZ`):
  with `a(t₀) ≠ 0` and `H₀ = 0` Lean's division by zero gives `q₀ = 0`, `j₀ = 0` and `Ω₀ = 1`, so the
  condition already fails. This redundancy exists only because of Lean's `x / 0 = 0`.
* **Smoothness, the lookback series** (`lookback_second_order`, `CCS.lookback_fifth_order`): the scale
  factors `1 + t + t|t|` and `1 + t + t⁴|t|` have one derivative too few at `0`; Lean's junk derivative
  there is `0`, so the series is built with `q₀ = 0` (resp. `l₀ = 0`) while the remainder is
  `t|t| + a z³` (resp. `t⁴|t| − a z⁶`), not `o(z²)` (resp. `o(z⁵)`): differentiability of `ȧ` at `t₀`
  and `C⁵` are needed. Eventual differentiability of `a` near `t₀` is redundant in
  `lookback_second_order`: a differentiable `ȧ` with `ȧ(t₀) ≠ 0` is nonzero near `t₀`, and a nonzero
  `deriv` value means `a` is differentiable there.
* **Smoothness, the distance series** (`BambaY.lumDist_y_third_order`, `CVdQ.dQ_y_third_order` with
  `1 + t + t²|t|`; `BambaK.lumDist_y_fifth_order`, `BambaA.angDist_y_fifth_order`,
  `BambaZ.lumDist_z_fifth_order`, `BambaZ.angDist_z_fifth_order` with `1 + t + t⁴|t|` and `K = 0`): the
  kinked scale factor has the same coefficients as `1 + t` (one of them a junk value), the series theorem
  holds for `1 + t`, and the two remainders differ by `tⁿ⁺¹|t|(1 + o(1)) + O(|t|ⁿ⁺³)`
  (`compare_general`, with the comoving distances compared by `comoving_bounds`), so the kinked
  remainder is not `o(·ⁿ⁺²)`: smoothness is needed.
* **Smoothness under an expansion law is redundant** (`Aviles.flatLCDM_coeffs`, `CPL.flatCPL_coeffs`,
  `CPL.printedL0_ne`, records `F1_l0`, `F2_toy`, `F2_error`, `F3_D4_LCDM`): the flat ΛCDM and CPL laws
  say `ȧ = Φ(a)` near `t₀` with `Φ` smooth near `a(t₀)`, and a bootstrap (`contDiffAt_of_law`: `a` is
  `Cᵏ` ⇒ `ȧ = Φ ∘ a` is `Cᵏ` ⇒ `a` is `Cᵏ⁺¹`) makes `a` smooth at `t₀`.
* **Local existence for an expansion law** (`CPLExistence.exists_local_model`): smoothness of the law
  is needed: for `E(x) = 1 + |x − 1|` a `C⁵` solution of `ȧ = a E(a)` would make `|a − 1|` differentiable
  at its minimum.
* **Printed `l₀`, `m₀`** (`AvilesWitness.printedL0_false_at`, `printedM0_false_at`): `0 < Ω` and
  `3Ω² + 2Ω − 2 ≠ 0` are needed: at `Ω = 0` and `Ω = (√7 − 1)/3` the printed coefficient is the correct
  one (`flatLCDM_coeffs`). `Ω < 1` is redundant there: a flat ΛCDM model exists for every `Ω`
  (`exists_flatLCDM_any`, from `CPLExistence.exists_local_model`).
* **The critical cubic** (`Chemistry.CubicEOS.critCubic_existsUnique`): `−2 < u` and `0 < 1 + u + w` are
  needed: `(x − 2)(x − 3)(x + 2)` (two roots above 1) and `(x − 1)³` (none).
  In `exists_unique_critical`, `0 < R` and `0 < a` are needed: with `R = 0` or `a = 0` the isotherm's
  slope never vanishes beyond the covolume.
* **The `f(R)` slow-roll ratios** (`FREta.eta20_hasDerivAt`, `FREta.eta30_hasDerivAt`): `0 < Ω` and `Ω < 1`
  are needed: at `Ω = 0` and `Ω = 2` the family's denominator vanishes at `ε = 0`, Lean's `x/0 = 0`
  gives `η(0) = 0`, but `εᵏ η(ε)` tends to a nonzero limit, so `η` has no derivative at `0`
  (`not_hasDerivAt_of`).
* **The separation pair** (`FalknerSkan.SeparationEqual.fs_separation_equal`): `f' = p` (hypotheses 1
  and 10) and the Falkner–Skan equation (3 and 12) are needed. The profile `p = 1 − (1 + η²)e^{−η²}`,
  `q = p' = 2η³e^{−η²}` meets every boundary, sign and decay condition; with `f = −q'/q` (`f(0) = 0`) it
  satisfies `q' = −f q` (the equation at `β = 0`) but not `f' = p`, and with `f = ∫₀^η p` it satisfies
  `f' = p` but no equation; paired with the separation solution, the two parameters differ.
-/

open Set Filter Topology Asymptotics Metric
open Checked.Cosmography Checked.Cosmography.Aviles

namespace Checked.Trust.NCD

/-! ### The model `a = 1 + t + c t³` at `t₀ = 0` -/

/-- `1 + t + c t³`. -/
noncomputable def cub (c : ℝ) (t : ℝ) : ℝ := 1 + t + c * t ^ 3

theorem cub_d1 (c : ℝ) : deriv (cub c) = fun t => 1 + 3 * c * t ^ 2 := by
  funext t
  have h : HasDerivAt (cub c) (1 + 3 * c * t ^ 2) t := by
    have := ((hasDerivAt_id' t).const_add 1).add ((hasDerivAt_pow 3 t).const_mul c)
    convert this using 1
    · funext y; simp only [cub, Pi.add_apply]
    · norm_num; ring
  exact h.deriv

theorem cub_d2 (c : ℝ) : deriv (deriv (cub c)) = fun t => 6 * c * t := by
  rw [cub_d1]; funext t
  have h : HasDerivAt (fun t : ℝ => 1 + 3 * c * t ^ 2) (6 * c * t) t := by
    have := ((hasDerivAt_pow 2 t).const_mul (3 * c)).const_add 1
    convert this using 1; push_cast; ring
  exact h.deriv

theorem cub_d3 (c : ℝ) : deriv (deriv (deriv (cub c))) = fun _ => 6 * c := by
  rw [cub_d2]; funext t
  have h : HasDerivAt (fun t : ℝ => 6 * c * t) (6 * c) t := by
    simpa using (hasDerivAt_id' t).const_mul (6 * c)
  exact h.deriv

theorem cub_smooth (c : ℝ) (n : ℕ∞) : ContDiffAt ℝ n (cub c) 0 := by
  have : ContDiff ℝ n (cub c) := by unfold cub; fun_prop
  exact this.contDiffAt

theorem cub_ne (c : ℝ) : cub c 0 ≠ 0 := by simp [cub]

theorem cub_hubble (c : ℝ) : hubble (cub c) 0 = 1 := by
  simp [hubble, cub_d1, cub]

theorem cub_decel (c : ℝ) : decel (cub c) 0 = 0 := by
  simp [decel, cub_d2]

theorem cub_j (c : ℝ) : cosmoCoeff 3 (cub c) 0 = 6 * c := by
  have h3 : iteratedDeriv 3 (cub c) = fun _ => 6 * c := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, cub_d3]
  simp [cosmoCoeff, h3, cub_hubble, cub]

/-! ### Static models: `H₀ = 0` forces `q₀ = 0`, `j₀ = 0`, `Ω₀ = 1` (division by zero) -/

theorem deriv_zero_of_hubble {a : ℝ → ℝ} {t₀ : ℝ} (ha0 : a t₀ ≠ 0) (h : hubble a t₀ = 0) :
    deriv a t₀ = 0 := by
  simpa [hubble, ha0] using h

theorem decel_zero_of_hubble {a : ℝ → ℝ} {t₀ : ℝ} (ha0 : a t₀ ≠ 0) (h : hubble a t₀ = 0) :
    decel a t₀ = 0 := by
  simp [decel, deriv_zero_of_hubble ha0 h]

theorem j_zero_of_hubble {a : ℝ → ℝ} {t₀ : ℝ} (h : hubble a t₀ = 0) : cosmoCoeff 3 a t₀ = 0 := by
  simp [cosmoCoeff, h]

theorem omega0_one_of_hubble {K : ℝ} {a : ℝ → ℝ} {t₀ : ℝ} (h : hubble a t₀ = 0) :
    BambaK.omega0 K a t₀ = 1 := by
  simp [BambaK.omega0, h]

theorem static_hubble : hubble (fun _ : ℝ => (1 : ℝ)) 0 = 0 := by simp [hubble]

/-! ### `CCS.printedD4_fails`, `CCS.printedD4_fails_past` (lookback time, Capozziello et al. 2008) -/

theorem ccs_printed_eq (a : ℝ → ℝ) (t₀ : ℝ) (hq : decel a t₀ = 0) (t : ℝ) :
    CCS.remainder CCS.correctD4 a t₀ t = CCS.remainder CCS.printedD4 a t₀ t := by
  simp only [CCS.remainder, CCS.printedD4, CCS.correctD4, hq]; ring

/-- The condition `q₀ ≠ 0` is needed in `CCS.printedD4_fails`: in `a = 1 + t` (`q₀ = 0`) the printed
`D⁴` is the correct one and the lookback series holds to fifth order. -/
theorem printedD4_fails_h4 : necessity% Checked.Cosmography.CCS.printedD4_fails 4 := by
  refine ⟨cub 0, 0, cub_smooth 0 _, cub_ne 0, by rw [cub_hubble]; norm_num, ?_⟩
  exact (CCS.lookback_fifth_order (cub 0) 0 (cub_smooth 0 _) (cub_ne 0) (by rw [cub_hubble]; norm_num)).congr'
    (Eventually.of_forall (ccs_printed_eq _ _ (cub_decel 0))) EventuallyEq.rfl

theorem printedD4_fails_past_h4 : necessity% Checked.Cosmography.CCS.printedD4_fails_past 4 := by
  refine ⟨cub 0, 0, cub_smooth 0 _, cub_ne 0, by rw [cub_hubble]; norm_num, ?_⟩
  exact ((CCS.lookback_fifth_order (cub 0) 0 (cub_smooth 0 _) (cub_ne 0)
    (by rw [cub_hubble]; norm_num)).mono nhdsWithin_le_nhds).congr'
    (Eventually.of_forall (ccs_printed_eq _ _ (cub_decel 0))) EventuallyEq.rfl

/-- `H₀ ≠ 0` is redundant in `CCS.printedD4_fails`: `q₀ ≠ 0` and `a(t₀) ≠ 0` imply it (division by zero). -/
theorem printedD4_fails_r3 : dropped% Checked.Cosmography.CCS.printedD4_fails 3 := by
  intro a t₀ ha ha0 hq
  exact CCS.printedD4_fails a t₀ ha ha0 (fun h => hq (decel_zero_of_hubble ha0 h)) hq

theorem printedD4_fails_past_r3 : dropped% Checked.Cosmography.CCS.printedD4_fails_past 3 := by
  intro a t₀ ha ha0 hq
  exact CCS.printedD4_fails_past a t₀ ha ha0 (fun h => hq (decel_zero_of_hubble ha0 h)) hq

/-! ### `BambaY.printedD2y_fails(_past)` and `CVdQ.printedQ2_fails_past` (third order in `y`) -/

/-- The condition `11 − 5q₀ + 3q₀² − j₀ ≠ 0` is needed in `BambaY.printedD2y_fails`: in
`a = 1 + t + (11/6) t³` (`q₀ = 0`, `j₀ = 11`) the printed `D²` equals the correct one (both zero). -/
theorem printedD2y_fails_h4 : necessity% Checked.Cosmography.BambaY.printedD2y_fails 4 := by
  refine ⟨cub (11 / 6), 0, cub_smooth _ _, cub_ne _, by rw [cub_hubble]; norm_num, ?_⟩
  refine (BambaY.lumDist_y_third_order (cub (11 / 6)) 0 (cub_smooth _ _) (cub_ne _)
    (by rw [cub_hubble]; norm_num)).congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
  simp only [BambaY.remainderY, BambaY.printedD2y, BambaY.correctD2y, cub_decel, cub_j]; norm_num

theorem printedD2y_fails_past_h4 : necessity% Checked.Cosmography.BambaY.printedD2y_fails_past 4 := by
  refine ⟨cub (11 / 6), 0, cub_smooth _ _, cub_ne _, by rw [cub_hubble]; norm_num, ?_⟩
  refine ((BambaY.lumDist_y_third_order (cub (11 / 6)) 0 (cub_smooth _ _) (cub_ne _)
    (by rw [cub_hubble]; norm_num)).mono nhdsWithin_le_nhds).congr'
    (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
  simp only [BambaY.remainderY, BambaY.printedD2y, BambaY.correctD2y, cub_decel, cub_j]; norm_num

/-- A nonzero Hubble rate is needed in `BambaY.printedD2y_fails_past`: the static model `a = 1`. -/
theorem printedD2y_fails_past_h3 : necessity% Checked.Cosmography.BambaY.printedD2y_fails_past 3 := by
  refine ⟨fun _ => 1, 0, contDiffAt_const, one_ne_zero, ?_, ?_⟩
  · simp [decel, cosmoCoeff, static_hubble]
  · have hz : ∀ t, BambaY.remainderY BambaY.printedD2y (fun _ : ℝ => (1 : ℝ)) 0 t = 0 := by
      intro t; simp [BambaY.remainderY, BambaY.seriesY, BambaY.yred, redshift, static_hubble]
    simp only [hz]
    exact isLittleO_zero _ _

/-- The condition `−1 − 2q₀ + 12q₀² − 4j₀ ≠ 0` is needed in `CVdQ.printedQ2_fails_past`: in
`a = 1 + t − t³/24` (`q₀ = 0`, `j₀ = −1/4`) the printed and correct `Q²` are both zero. -/
theorem printedQ2_fails_past_h4 : necessity% Checked.Cosmography.CVdQ.printedQ2_fails_past 4 := by
  refine ⟨cub (-1 / 24), 0, cub_smooth _ _, cub_ne _, by rw [cub_hubble]; norm_num, ?_⟩
  refine ((CVdQ.dQ_y_third_order (cub (-1 / 24)) 0 (cub_smooth _ _) (cub_ne _)
    (by rw [cub_hubble]; norm_num)).mono nhdsWithin_le_nhds).congr'
    (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
  simp only [CVdQ.remainderQ, CVdQ.printedQ2, CVdQ.correctQ2, cub_decel, cub_j]; norm_num

/-- A nonzero Hubble rate is needed in `CVdQ.printedQ2_fails_past`: the static model `a = 1`. -/
theorem printedQ2_fails_past_h3 : necessity% Checked.Cosmography.CVdQ.printedQ2_fails_past 3 := by
  refine ⟨fun _ => 1, 0, contDiffAt_const, one_ne_zero, ?_, ?_⟩
  · simp [decel, cosmoCoeff, static_hubble]
  · have hz : ∀ t, CVdQ.remainderQ CVdQ.printedQ2 (fun _ : ℝ => (1 : ℝ)) 0 t = 0 := by
      intro t; simp [CVdQ.remainderQ, CVdQ.seriesQ, BambaY.yred, redshift, static_hubble]
    simp only [hz]
    exact isLittleO_zero _ _

/-! ### Curvature corrections (`BambaK`, `BambaA`): zero curvature makes printed = correct -/

theorem omega0_flat (a : ℝ → ℝ) (t₀ : ℝ) : BambaK.omega0 0 a t₀ = 1 := by simp [BambaK.omega0]

theorem y5_y4 (a : ℝ → ℝ) (t₀ : ℝ) (hd : DifferentiableAt ℝ a t₀) (ha0 : a t₀ ≠ 0) :
    (fun t => BambaY.yred a t₀ t ^ 5) =o[𝓝 t₀] (fun t => BambaY.yred a t₀ t ^ 4) := by
  simpa using BambaY.pow_succ_mul_isLittleO (BambaA.yred_tendsto a t₀ hd ha0) 4 (fun _ => (1 : ℝ))
    (isBigO_refl _ _)

theorem cub_diff : DifferentiableAt ℝ (cub 0) 0 := (cub_smooth 0 1).differentiableAt (by norm_num)

/-- The condition `(Ω₀ − 1)(3q₀ − 2) ≠ 0` is needed in `BambaK.printedD3y_fails`: with zero curvature
(`Ω₀ = 1`) the printed `D³` is the correct one, and the fifth-order series gives `o(y⁴)`. -/
theorem printedD3y_fails_h4 : necessity% Checked.Cosmography.BambaK.printedD3y_fails 4 := by
  refine ⟨0, cub 0, 0, cub_smooth 0 _, cub_ne 0, by rw [cub_hubble]; norm_num, ?_⟩
  have hc := BambaK.lumDist_y_fifth_order 0 (cub 0) 0 (cub_smooth 0 _) (cub_ne 0) (by rw [cub_hubble]; norm_num)
  have h54 := y5_y4 (cub 0) 0 cub_diff (cub_ne 0)
  refine ((hc.trans h54).add (h54.const_mul_left (BambaK.correctD4y (decel (cub 0) 0)
    (cosmoCoeff 3 (cub 0) 0) (cosmoCoeff 4 (cub 0) 0) (cosmoCoeff 5 (cub 0) 0) 1))).congr'
    (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
  simp only [BambaK.remK, BambaK.seriesY4, BambaK.correctD3y, omega0_flat]; ring

theorem printedD3y_fails_past_h4 : necessity% Checked.Cosmography.BambaK.printedD3y_fails_past 4 := by
  obtain ⟨K, a, t₀, ha, ha0, hH, h⟩ := printedD3y_fails_h4
  exact ⟨K, a, t₀, ha, ha0, hH, h.mono nhdsWithin_le_nhds⟩

/-- The condition `(Ω₀ − 1)²/120 + 5q₀(Ω₀ − 1)/12 ≠ 0` is needed in `BambaK.printedD4y_fails`: with
zero curvature the printed `D⁴` is the correct one. -/
theorem printedD4y_fails_h4 : necessity% Checked.Cosmography.BambaK.printedD4y_fails 4 := by
  refine ⟨0, cub 0, 0, cub_smooth 0 _, cub_ne 0, by rw [cub_hubble]; norm_num, ?_⟩
  refine (BambaK.lumDist_y_fifth_order 0 (cub 0) 0 (cub_smooth 0 _) (cub_ne 0)
    (by rw [cub_hubble]; norm_num)).congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
  simp only [BambaK.remK, BambaK.correctD4y, omega0_flat]; ring

theorem printedD4y_fails_past_h4 : necessity% Checked.Cosmography.BambaK.printedD4y_fails_past 4 := by
  obtain ⟨K, a, t₀, ha, ha0, hH, h⟩ := printedD4y_fails_h4
  exact ⟨K, a, t₀, ha, ha0, hH, h.mono nhdsWithin_le_nhds⟩

/-- `H₀ ≠ 0` is redundant in `BambaK.printedD3y_fails`: `H₀ = 0` gives `Ω₀ = 1` (division by zero). -/
theorem printedD3y_fails_r3 : dropped% Checked.Cosmography.BambaK.printedD3y_fails 3 := by
  intro K a t₀ ha ha0 hD
  exact BambaK.printedD3y_fails K a t₀ ha ha0 (fun h => hD (by rw [omega0_one_of_hubble h]; ring)) hD

theorem printedD3y_fails_past_r3 : dropped% Checked.Cosmography.BambaK.printedD3y_fails_past 3 := by
  intro K a t₀ ha ha0 hD
  exact BambaK.printedD3y_fails_past K a t₀ ha ha0 (fun h => hD (by rw [omega0_one_of_hubble h]; ring)) hD

theorem printedD4y_fails_r3 : dropped% Checked.Cosmography.BambaK.printedD4y_fails 3 := by
  intro K a t₀ ha ha0 hD
  exact BambaK.printedD4y_fails K a t₀ ha ha0 (fun h => hD (by rw [omega0_one_of_hubble h]; ring)) hD

theorem printedD4y_fails_past_r3 : dropped% Checked.Cosmography.BambaK.printedD4y_fails_past 3 := by
  intro K a t₀ ha ha0 hD
  exact BambaK.printedD4y_fails_past K a t₀ ha ha0 (fun h => hD (by rw [omega0_one_of_hubble h]; ring)) hD

/-- The condition `q₀(Ω₀ − 1) ≠ 0` is needed in `BambaA.printedDA3_fails`: zero curvature. -/
theorem printedDA3_fails_h4 : necessity% Checked.Cosmography.BambaA.printedDA3_fails 4 := by
  refine ⟨0, cub 0, 0, cub_smooth 0 _, cub_ne 0, by rw [cub_hubble]; norm_num, ?_⟩
  have hc := BambaA.angDist_y_fifth_order 0 (cub 0) 0 (cub_smooth 0 _) (cub_ne 0) (by rw [cub_hubble]; norm_num)
  have h54 := y5_y4 (cub 0) 0 cub_diff (cub_ne 0)
  refine ((hc.trans h54).add (h54.const_mul_left (BambaA.correctDA4 (decel (cub 0) 0)
    (cosmoCoeff 3 (cub 0) 0) (cosmoCoeff 4 (cub 0) 0) (cosmoCoeff 5 (cub 0) 0) 1))).congr'
    (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
  simp only [BambaA.remA, BambaA.correctDA3, omega0_flat]; ring

theorem printedDA3_fails_past_h4 : necessity% Checked.Cosmography.BambaA.printedDA3_fails_past 4 := by
  obtain ⟨K, a, t₀, ha, ha0, hH, h⟩ := printedDA3_fails_h4
  exact ⟨K, a, t₀, ha, ha0, hH, h.mono nhdsWithin_le_nhds⟩

/-- The condition `(Ω₀ − 1)((Ω₀ − 1) + 10j₀ − 45q₀² + 20q₀) ≠ 0` is needed in
`BambaA.printedDA4_fails`: zero curvature. -/
theorem printedDA4_fails_h4 : necessity% Checked.Cosmography.BambaA.printedDA4_fails 4 := by
  refine ⟨0, cub 0, 0, cub_smooth 0 _, cub_ne 0, by rw [cub_hubble]; norm_num, ?_⟩
  refine (BambaA.angDist_y_fifth_order 0 (cub 0) 0 (cub_smooth 0 _) (cub_ne 0)
    (by rw [cub_hubble]; norm_num)).congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
  simp only [BambaA.remA, BambaA.correctDA4, omega0_flat]; ring

theorem printedDA4_fails_past_h4 : necessity% Checked.Cosmography.BambaA.printedDA4_fails_past 4 := by
  obtain ⟨K, a, t₀, ha, ha0, hH, h⟩ := printedDA4_fails_h4
  exact ⟨K, a, t₀, ha, ha0, hH, h.mono nhdsWithin_le_nhds⟩

theorem printedDA3_fails_r3 : dropped% Checked.Cosmography.BambaA.printedDA3_fails 3 := by
  intro K a t₀ ha ha0 hD
  exact BambaA.printedDA3_fails K a t₀ ha ha0 (fun h => hD (by rw [omega0_one_of_hubble h]; ring)) hD

theorem printedDA3_fails_past_r3 : dropped% Checked.Cosmography.BambaA.printedDA3_fails_past 3 := by
  intro K a t₀ ha ha0 hD
  exact BambaA.printedDA3_fails_past K a t₀ ha ha0 (fun h => hD (by rw [omega0_one_of_hubble h]; ring)) hD

theorem printedDA4_fails_r3 : dropped% Checked.Cosmography.BambaA.printedDA4_fails 3 := by
  intro K a t₀ ha ha0 hD
  exact BambaA.printedDA4_fails K a t₀ ha ha0 (fun h => hD (by rw [omega0_one_of_hubble h]; ring)) hD

theorem printedDA4_fails_past_r3 : dropped% Checked.Cosmography.BambaA.printedDA4_fails_past 3 := by
  intro K a t₀ ha ha0 hD
  exact BambaA.printedDA4_fails_past K a t₀ ha ha0 (fun h => hD (by rw [omega0_one_of_hubble h]; ring)) hD

/-! ### Series in `z` (`BambaZ`, `DemianskiZ`) -/

theorem curvK_flat (a : ℝ → ℝ) (t₀ : ℝ) : BambaZ.curvK 0 a t₀ = 0 := by simp [BambaZ.curvK]

/-- The condition `K ≠ 0` is needed in `BambaZ.printedDL4z_fails_past`: with `K = 0` the printed
`D⁴_L` is the correct one. -/
theorem printedDL4z_fails_past_h4 : necessity% Checked.Cosmography.BambaZ.printedDL4z_fails_past 4 := by
  refine ⟨0, cub 0, 0, cub_smooth 0 _, cub_ne 0, by rw [cub_hubble]; norm_num, ?_⟩
  refine ((BambaZ.lumDist_z_fifth_order 0 (cub 0) 0 (cub_smooth 0 _) (cub_ne 0)
    (by rw [cub_hubble]; norm_num)).mono nhdsWithin_le_nhds).congr'
    (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
  simp only [BambaZ.remLz, BambaZ.correctDL4z, curvK_flat]; ring

theorem printedDA4z_fails_past_h4 : necessity% Checked.Cosmography.BambaZ.printedDA4z_fails_past 4 := by
  refine ⟨0, cub 0, 0, cub_smooth 0 _, cub_ne 0, by rw [cub_hubble]; norm_num, ?_⟩
  refine ((BambaZ.angDist_z_fifth_order 0 (cub 0) 0 (cub_smooth 0 _) (cub_ne 0)
    (by rw [cub_hubble]; norm_num)).mono nhdsWithin_le_nhds).congr'
    (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
  simp only [BambaZ.remAz, BambaZ.correctDA4z, curvK_flat]; ring

/-- A nonzero Hubble rate is needed in `BambaZ.printedDL4z_fails_past`: the static model `a = 1`
with `K = 1`. -/
theorem printedDL4z_fails_past_h3 : necessity% Checked.Cosmography.BambaZ.printedDL4z_fails_past 3 := by
  refine ⟨1, fun _ => 1, 0, contDiffAt_const, one_ne_zero, one_ne_zero, ?_⟩
  have hz : ∀ t, BambaZ.remLz BambaZ.printedDL4z 1 (fun _ : ℝ => (1 : ℝ)) 0 t = 0 := by
    intro t; simp [BambaZ.remLz, BambaZ.seriesZ, redshift, static_hubble]
  simp only [hz]
  exact isLittleO_zero _ _

theorem printedDA4z_fails_past_h3 : necessity% Checked.Cosmography.BambaZ.printedDA4z_fails_past 3 := by
  refine ⟨1, fun _ => 1, 0, contDiffAt_const, one_ne_zero, one_ne_zero, ?_⟩
  have hz : ∀ t, BambaZ.remAz BambaZ.printedDA4z 1 (fun _ : ℝ => (1 : ℝ)) 0 t = 0 := by
    intro t; simp [BambaZ.remAz, BambaZ.seriesZ, redshift, static_hubble]
  simp only [hz]
  exact isLittleO_zero _ _

/-- The condition `q₀ ≠ 0` is needed in `DemianskiZ.demDL4_fails_past`: in `a = 1 + t` the printed
`D⁴_L` equals the correct flat one. -/
theorem demDL4_fails_past_h4 : necessity% Checked.Cosmography.DemianskiZ.demDL4_fails_past 4 := by
  refine ⟨cub 0, 0, cub_smooth 0 _, cub_ne 0, by rw [cub_hubble]; norm_num, ?_⟩
  refine ((BambaZ.lumDist_z_fifth_order 0 (cub 0) 0 (cub_smooth 0 _) (cub_ne 0)
    (by rw [cub_hubble]; norm_num)).mono nhdsWithin_le_nhds).congr'
    (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
  simp only [BambaZ.remLz, BambaZ.correctDL4z, BambaZ.printedDL4z, DemianskiZ.demDL4, curvK_flat,
    cub_decel]; ring

/-- The condition `j₀ ≠ 0` is needed in `DemianskiZ.demDA4_fails_past`: in `a = 1 + t` (`j₀ = 0`)
the printed `D⁴_A` equals the correct flat one. -/
theorem demDA4_fails_past_h4 : necessity% Checked.Cosmography.DemianskiZ.demDA4_fails_past 4 := by
  refine ⟨cub 0, 0, cub_smooth 0 _, cub_ne 0, by rw [cub_hubble]; norm_num, ?_⟩
  refine ((BambaZ.angDist_z_fifth_order 0 (cub 0) 0 (cub_smooth 0 _) (cub_ne 0)
    (by rw [cub_hubble]; norm_num)).mono nhdsWithin_le_nhds).congr'
    (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
  have hj : cosmoCoeff 3 (cub 0) 0 = 0 := by rw [cub_j]; ring
  simp only [BambaZ.remAz, BambaZ.correctDA4z, BambaZ.printedDA4z, DemianskiZ.demDA4, curvK_flat,
    hj]; ring

/-- `H₀ ≠ 0` is redundant in `DemianskiZ.demDL4_fails_past`: `q₀ ≠ 0` implies it (division by zero). -/
theorem demDL4_fails_past_r3 : dropped% Checked.Cosmography.DemianskiZ.demDL4_fails_past 3 := by
  intro a t₀ ha ha0 hq
  exact DemianskiZ.demDL4_fails_past a t₀ ha ha0 (fun h => hq (decel_zero_of_hubble ha0 h)) hq

/-- `H₀ ≠ 0` is redundant in `DemianskiZ.demDA4_fails_past`: `j₀ ≠ 0` implies it (division by zero). -/
theorem demDA4_fails_past_r3 : dropped% Checked.Cosmography.DemianskiZ.demDA4_fails_past 3 := by
  intro a t₀ ha ha0 hj
  exact DemianskiZ.demDA4_fails_past a t₀ ha ha0 (fun h => hj (j_zero_of_hubble h)) hj

/-! ### Scale factors with one derivative too few: `1 + t + tⁿ|t|` -/

/-- `t^(n+1) |t|` has derivative `(n + 2) xⁿ |x|` at every `x`. -/
theorem pabs_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ (n + 1) * |t|) ((n + 2) * x ^ n * |x|) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have h := (hasDerivAt_pow (n + 1) x).mul (hasDerivAt_abs_neg hx)
    convert h using 1
    rw [abs_of_neg hx]; simp only [Nat.add_sub_cancel]; push_cast; ring
  · have h1 : HasDerivWithinAt (fun t : ℝ => t ^ (n + 1) * |t|) 0 (Ici 0) 0 := by
      have := (hasDerivAt_pow (n + 2) (0 : ℝ)).hasDerivWithinAt (s := Ici 0)
      refine (this.congr (fun t ht => ?_) (by simp)).congr_deriv (by simp)
      simp only [mem_Ici] at ht
      simp only [abs_of_nonneg ht]; ring
    have h2 : HasDerivWithinAt (fun t : ℝ => t ^ (n + 1) * |t|) 0 (Iic 0) 0 := by
      have := ((hasDerivAt_pow (n + 2) (0 : ℝ)).neg).hasDerivWithinAt (s := Iic 0)
      refine (this.congr (fun t ht => ?_) (by simp)).congr_deriv (by simp)
      simp only [mem_Iic] at ht
      simp only [abs_of_nonpos ht, Pi.neg_apply]; ring
    have := h1.union h2
    rw [Ici_union_Iic, hasDerivWithinAt_univ] at this
    convert this using 1; simp
  · have h := (hasDerivAt_pow (n + 1) x).mul (hasDerivAt_abs_pos hx)
    convert h using 1
    rw [abs_of_pos hx]; simp only [Nat.add_sub_cancel]; push_cast; ring

theorem pabs_deriv (n : ℕ) (c : ℝ) :
    deriv (fun t : ℝ => c * (t ^ (n + 1) * |t|)) = fun x => c * (n + 2) * (x ^ n * |x|) := by
  funext x; rw [((pabs_hasDerivAt n x).const_mul c).deriv]; ring

/-- `1 + t + tⁿ⁺¹|t|`: `C^(n+1)` but not `C^(n+2)` at `0`. -/
noncomputable def kink (n : ℕ) (t : ℝ) : ℝ := 1 + t + t ^ (n + 1) * |t|

theorem kink_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (kink n) (1 + (n + 2) * (x ^ n * |x|)) x := by
  have := ((hasDerivAt_id' x).const_add 1).add (pabs_hasDerivAt n x)
  convert this using 1
  · funext t; simp only [kink, Pi.add_apply]
  · ring

theorem kink_deriv (n : ℕ) : deriv (kink n) = fun x : ℝ => 1 + ((n : ℝ) + 2) * (x ^ n * |x|) := by
  funext x; exact (kink_hasDerivAt n x).deriv

theorem kink_ne (n : ℕ) : kink n 0 ≠ 0 := by simp [kink]

theorem kink_hubble (n : ℕ) : hubble (kink n) 0 = 1 := by
  rw [hubble, kink_deriv]; simp [kink]

/-- The algebra of the lookback remainder in `kink n`: with `z = 1/a − 1` and `a = 1 + t + g`,
`−t − z(1 − z + … ± zⁿ) = g ± a zⁿ⁺¹`. Fifth order: `−t − z(1 − z + z² − z³ + z⁴) = g − a z⁶`. -/
theorem kink_z (n : ℕ) (t : ℝ) (ha : kink n t ≠ 0) :
    redshift (kink n) 0 t = 1 / kink n t - 1 := by
  simp [redshift, kink]

/-- Near `0`, `|z| ≤ 4|t|` and `kink n` stays above `1/2`. -/
theorem kink_bounds (n : ℕ) : ∀ᶠ t in 𝓝 (0 : ℝ), 1 / 2 ≤ kink n t ∧
    |redshift (kink n) 0 t| ≤ 4 * |t| := by
  have hlt : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < 1 / 4 := by
    have : Iio (1 / 4 : ℝ) ∈ 𝓝 |(0 : ℝ)| := Iio_mem_nhds (by norm_num)
    exact (continuous_abs.continuousAt.preimage_mem_nhds this)
  filter_upwards [hlt] with t ht
  have hn : abs (t ^ (n + 1) * |t|) ≤ |t| := by
    rw [abs_mul, abs_abs, abs_pow]
    have h1 : |t| ^ (n + 1) ≤ 1 := pow_le_one₀ (abs_nonneg t) (by linarith)
    nlinarith [abs_nonneg t]
  have hg := abs_le.1 hn
  have ht' := abs_lt.1 ht
  have hk : 1 / 2 ≤ kink n t := by
    unfold kink; nlinarith [abs_nonneg t]
  refine ⟨hk, ?_⟩
  have hpos : 0 < kink n t := by linarith
  rw [kink_z n t hpos.ne']
  have hz : 1 / kink n t - 1 = -(t + t ^ (n + 1) * |t|) / kink n t := by
    field_simp; unfold kink; ring
  rw [hz, abs_div, abs_of_pos hpos, div_le_iff₀ hpos, abs_neg]
  have : abs (t + t ^ (n + 1) * |t|) ≤ 2 * |t| := by
    calc abs (t + t ^ (n + 1) * |t|) ≤ |t| + abs (t ^ (n + 1) * |t|) := abs_add_le _ _
      _ ≤ 2 * |t| := by linarith
  nlinarith [abs_nonneg t]

/-- If `tⁿ⁺¹|t| = o(zⁿ⁺¹)` in `kink n`, contradiction: `|z| ≤ 4|t|`. -/
theorem kink_not_littleO (n : ℕ) :
    ¬ (fun t : ℝ => t ^ (n + 1) * |t|) =o[𝓝 0] (fun t => redshift (kink n) 0 t ^ (n + 2)) := by
  intro h
  have hc : (0 : ℝ) < 1 / (2 * 4 ^ (n + 2)) := by positivity
  have h1 := h.def hc
  have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), t = 0 := by
    filter_upwards [h1, kink_bounds n] with t ht hb
    have hz : |redshift (kink n) 0 t| ^ (n + 2) ≤ (4 * |t|) ^ (n + 2) :=
      pow_le_pow_left₀ (abs_nonneg _) hb.2 _
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_abs] at ht
    rw [mul_pow] at hz
    have h4 : (0 : ℝ) < 4 ^ (n + 2) := by positivity
    have key : |t| ^ (n + 1) * |t| ≤ |t| ^ (n + 1) * |t| / 2 := by
      calc |t| ^ (n + 1) * |t| ≤ 1 / (2 * 4 ^ (n + 2)) * |redshift (kink n) 0 t| ^ (n + 2) := ht
        _ ≤ 1 / (2 * 4 ^ (n + 2)) * (4 ^ (n + 2) * |t| ^ (n + 2)) := by gcongr
        _ = |t| ^ (n + 1) * |t| / 2 := by field_simp; ring
    have : |t| ^ (n + 1) * |t| ≤ 0 := by linarith
    have : |t| ^ (n + 2) = 0 := by
      apply le_antisymm _ (by positivity); rw [pow_succ]; exact this
    simpa using this
  have hne : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0 := self_mem_nhdsWithin
  have := (h2.filter_mono nhdsWithin_le_nhds).and hne
  exact (this.exists).elim fun t ht => ht.2 ht.1

theorem kink_cont (n : ℕ) : Continuous (kink n) := by unfold kink; fun_prop

theorem kink_z_tendsto (n : ℕ) : Tendsto (fun t => redshift (kink n) 0 t) (𝓝 0) (𝓝 0) := by
  have h4 : Tendsto (fun t : ℝ => 4 * |t|) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs.tendsto (0 : ℝ)).const_mul 4
  refine squeeze_zero_norm' ?_ h4
  filter_upwards [kink_bounds n] with t ht
  simpa [Real.norm_eq_abs] using ht.2

/-- `a z^(m+1) = o(z^m)` in `kink n`. -/
theorem kink_az (n m : ℕ) : (fun t => kink n t * redshift (kink n) 0 t ^ (m + 1)) =o[𝓝 0]
    (fun t => redshift (kink n) 0 t ^ m) := by
  have ht : Tendsto (fun t => kink n t * redshift (kink n) 0 t) (𝓝 0) (𝓝 0) := by
    simpa using ((kink_cont n).tendsto 0).mul (kink_z_tendsto n)
  have := (isLittleO_one_iff ℝ).2 ht |>.mul_isBigO (isBigO_refl (fun t => redshift (kink n) 0 t ^ m) (𝓝 0))
  refine this.congr' (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t => ?_) <;>
    simp only [one_mul] <;> ring

/-- The remainder of the second-order lookback series in `kink 0` (`a = 1 + t + t|t|`):
`−t − z + z² = t|t| + a z³`. -/
theorem kink0_rem : ∀ᶠ t in 𝓝 (0 : ℝ),
    (0 - t) - (redshift (kink 0) 0 t - (1 + 0 / 2) * redshift (kink 0) 0 t ^ 2) / 1 =
      t ^ (0 + 1) * |t| + kink 0 t * redshift (kink 0) 0 t ^ 3 := by
  filter_upwards [kink_bounds 0] with t ht
  have hpos : kink 0 t ≠ 0 := by linarith [ht.1]
  rw [kink_z 0 t hpos]
  field_simp
  unfold kink; ring

theorem kink0_deriv2 : deriv (deriv (kink 0)) 0 = 0 := by
  rw [kink_deriv]
  have : (fun x : ℝ => 1 + ((0 : ℕ) + 2 : ℝ) * (x ^ 0 * |x|)) = fun x => 1 + 2 * |x| := by
    funext x; norm_num
  rw [this]
  apply deriv_zero_of_not_differentiableAt
  intro h
  apply not_differentiableAt_abs_zero
  have := (h.const_add (-1)).const_mul (1 / 2 : ℝ)
  convert this using 1; funext x; ring

/-- Differentiability of `ȧ` at `t₀` is needed in `lookback_second_order`: `a = 1 + t + t|t|` is
differentiable with `ȧ(0) = 1`, but `ȧ = 1 + 2|t|` has no derivative at `0`; Lean's junk value
`ä(0) = 0` gives `q₀ = 0`, and the remainder is `t|t| + a z³`, not `o(z²)`. -/
theorem lookback_second_order_h2 : necessity% Checked.Cosmography.lookback_second_order 2 := by
  refine ⟨kink 0, 0, Eventually.of_forall fun t => (kink_hasDerivAt 0 t).differentiableAt,
    kink_ne 0, by rw [kink_deriv]; norm_num, ?_⟩
  intro h
  have hH : hubble (kink 0) 0 = 1 := kink_hubble 0
  have hq : decel (kink 0) 0 = 0 := by simp [decel, kink0_deriv2]
  rw [hH, hq] at h
  have hg := (h.congr' kink0_rem EventuallyEq.rfl).sub (kink_az 0 2)
  apply kink_not_littleO 0
  refine hg.congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
  ring

/-- Eventual differentiability of `a` is redundant in `lookback_second_order`: `ȧ` differentiable at
`t₀` with `ȧ(t₀) ≠ 0` is continuous there, so `ȧ ≠ 0` near `t₀`, and a nonzero `deriv` value means
`a` is differentiable (Lean's junk derivative is `0`). -/
theorem lookback_second_order_r1 : dropped% Checked.Cosmography.lookback_second_order 1 := by
  intro a t₀ ha' ha0 hH
  exact lookback_second_order a t₀ ((ha'.continuousAt.eventually_ne hH).mono
    fun t ht => differentiableAt_of_deriv_ne_zero ht) ha' ha0 hH

/-! ### Fifth order: `kink 3` (`a = 1 + t + t⁴|t|`, `C⁴` but not `C⁵`) -/

theorem kink3_d1 : deriv (kink 3) = fun x : ℝ => 1 + 5 * (x ^ 3 * |x|) := by
  rw [kink_deriv]; funext x; norm_num

theorem kink3_d2 : deriv (fun x : ℝ => 1 + 5 * (x ^ 3 * |x|)) = fun x => 20 * (x ^ 2 * |x|) := by
  funext x; apply HasDerivAt.deriv
  have := ((pabs_hasDerivAt 2 x).const_mul 5).const_add 1
  convert this using 1; push_cast; ring

theorem kink3_d3 : deriv (fun x : ℝ => 20 * (x ^ 2 * |x|)) = fun x => 60 * (x * |x|) := by
  funext x; apply HasDerivAt.deriv
  have := (pabs_hasDerivAt 1 x).const_mul 20
  convert this using 1; push_cast; ring

theorem kink3_d4 : deriv (fun x : ℝ => 60 * (x * |x|)) = fun x => 120 * |x| := by
  funext x; apply HasDerivAt.deriv
  have := (pabs_hasDerivAt 0 x).const_mul 60
  convert this using 1
  · funext t; ring
  · push_cast; ring

theorem kink3_d5 : deriv (fun x : ℝ => 120 * |x|) 0 = 0 := by
  rw [deriv_const_mul_field']; simp [deriv_abs_zero]

theorem kink3_coeffs : decel (kink 3) 0 = 0 ∧ cosmoCoeff 3 (kink 3) 0 = 0 ∧
    cosmoCoeff 4 (kink 3) 0 = 0 ∧ cosmoCoeff 5 (kink 3) 0 = 0 := by
  have i3 : iteratedDeriv 3 (kink 3) 0 = 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, kink3_d1, kink3_d2, kink3_d3]; simp
  have i4 : iteratedDeriv 4 (kink 3) 0 = 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, kink3_d1,
      kink3_d2, kink3_d3, kink3_d4]; simp
  have i5 : iteratedDeriv 5 (kink 3) 0 = 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
      iteratedDeriv_one, kink3_d1, kink3_d2, kink3_d3, kink3_d4, kink3_d5]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [decel, kink3_d1, kink3_d2]; simp
  all_goals simp [cosmoCoeff, i3, i4, i5]

/-- Fifth-order lookback remainder in `kink 3`: `−t − z(1 − z + z² − z³ + z⁴) = t⁴|t| − a z⁶`. -/
theorem kink3_rem : ∀ᶠ t in 𝓝 (0 : ℝ), CCS.remainder CCS.correctD4 (kink 3) 0 t =
    t ^ (3 + 1) * |t| - kink 3 t * redshift (kink 3) 0 t ^ (5 + 1) := by
  filter_upwards [kink_bounds 3] with t ht
  have hpos : kink 3 t ≠ 0 := by linarith [ht.1]
  obtain ⟨hq, hj, hs, hl⟩ := kink3_coeffs
  have hz1 : kink 3 t * (1 + redshift (kink 3) 0 t) = 1 := by
    rw [kink_z 3 t hpos]; field_simp; ring
  simp only [CCS.remainder, CCS.series, CCS.correctD4, CCS.D1, CCS.D2, CCS.D3, hq, hj, hs, hl,
    kink_hubble]
  set z := redshift (kink 3) 0 t
  have hk : kink 3 t = 1 + t + t ^ 4 * |t| := rfl
  rw [hk] at hz1 ⊢
  linear_combination (z ^ 5 - z ^ 4 + z ^ 3 - z ^ 2 + z - 1) * hz1

/-- Smoothness (`C⁵` at `t₀`) is needed in `CCS.lookback_fifth_order`: `a = 1 + t + t⁴|t|` is `C⁴`
with `ȧ(0) = 1`; its fourth derivative `120|t|` has no derivative at `0`, Lean's junk value gives
`l₀ = 0`, and the remainder is `t⁴|t| − a z⁶`, not `o(z⁵)`. -/
theorem lookback_fifth_order_h1 : necessity% Checked.Cosmography.CCS.lookback_fifth_order 1 := by
  refine ⟨kink 3, 0, kink_ne 3, by rw [kink_hubble]; norm_num, fun h => ?_⟩
  have hg := (h.congr' kink3_rem EventuallyEq.rfl).add (kink_az 3 5)
  apply kink_not_littleO 3
  refine hg.congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
  ring

/-- **Bootstrap.** If near `t₀` the function `a` is differentiable with `ȧ = Φ(a)`, and `Φ` is `Cⁿ`
near `a(t₀)`, then `a` is `Cⁿ` at `t₀`. -/
theorem contDiffAt_of_law (n : ℕ) (a Φ : ℝ → ℝ) (t₀ : ℝ)
    (hΦ : ∀ᶠ x in 𝓝 (a t₀), ContDiffAt ℝ n Φ x)
    (hd : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ a t ∧ deriv a t = Φ (a t)) :
    ContDiffAt ℝ n a t₀ := by
  have hac : ContinuousAt a t₀ := hd.self_of_nhds.1.continuousAt
  have hW : {t | DifferentiableAt ℝ a t ∧ deriv a t = Φ (a t)} ∩
      a ⁻¹' {x | ContDiffAt ℝ n Φ x} ∈ 𝓝 t₀ :=
    Filter.inter_mem hd (hac.preimage_mem_nhds hΦ)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hW
  set I := ball t₀ δ with hI
  have hIo : IsOpen I := isOpen_ball
  have hder : ∀ t ∈ I, HasDerivAt a (Φ (a t)) t := fun t ht => by
    rw [← (hball ht).1.2]; exact (hball ht).1.1.hasDerivAt
  have hgood : ∀ t ∈ I, ContDiffAt ℝ n Φ (a t) := fun t ht => (hball ht).2
  have key : ∀ k : ℕ, k ≤ n → ContDiffOn ℝ k a I := by
    intro k
    induction k with
    | zero =>
      intro _
      exact contDiffOn_zero.2 fun t ht => (hder t ht).continuousAt.continuousWithinAt
    | succ k ih =>
      intro hk
      have hk' : ContDiffOn ℝ k a I := ih (by omega)
      rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen hIo]
      refine ⟨fun t ht => (hder t ht).differentiableAt.differentiableWithinAt, ?_, ?_⟩
      · intro h; exact absurd h (by simp)
      · have hc : ContDiffOn ℝ k (fun t => Φ (a t)) I := by
          intro t ht
          have h1 : ContDiffAt ℝ k a t := hk'.contDiffAt (hIo.mem_nhds ht)
          have h2 : ContDiffAt ℝ k Φ (a t) :=
            (hgood t ht).of_le (by exact_mod_cast (show k ≤ n by omega))
          exact (h2.comp t h1).contDiffWithinAt
        exact hc.congr fun t ht => (hder t ht).deriv
  exact (key n le_rfl).contDiffAt (hIo.mem_nhds (mem_ball_self hδ))

/-- A flat ΛCDM expansion law makes the scale factor smooth at `t₀` (every finite order). -/
theorem contDiffAt_of_flatLCDM {Ω : ℝ} {a : ℝ → ℝ} {t₀ : ℝ} (hL : IsFlatLCDM Ω a t₀) (n : ℕ) :
    ContDiffAt ℝ n a t₀ := by
  obtain ⟨-, hev⟩ := hL
  have ha0 : 0 < a t₀ := hev.self_of_nhds.1
  set H := hubble a t₀
  set g : ℝ → ℝ := fun x => Ω * (a t₀ / x) ^ 3 + 1 - Ω with hg
  refine contDiffAt_of_law n a (fun x => x * H * √(g x)) t₀ ?_ ?_
  · have hgc : ContinuousAt g (a t₀) := by
      simp only [hg]
      exact ((continuousAt_const.div continuousAt_id ha0.ne').pow 3 |>.const_mul Ω |>.add
        continuousAt_const).sub continuousAt_const
    have hg1 : g (a t₀) = 1 := by simp only [hg]; field_simp; ring
    have hne : ∀ᶠ x in 𝓝 (a t₀), g x ≠ 0 := hgc.eventually_ne (by rw [hg1]; norm_num)
    have hx0 : ∀ᶠ x in 𝓝 (a t₀), x ≠ 0 := continuousAt_id.eventually_ne ha0.ne'
    filter_upwards [hne, hx0] with x hx hx0
    have hgs : ContDiffAt ℝ n g x := by
      simp only [hg]
      exact ((contDiffAt_const.div contDiffAt_id hx0).pow 3 |>.const_smul Ω |>.add
        contDiffAt_const).sub contDiffAt_const
    exact (contDiffAt_id.mul contDiffAt_const).mul (hgs.sqrt hx)
  · filter_upwards [hev] with t ⟨hpos, hdt, hh⟩
    refine ⟨hdt, ?_⟩
    have h1 : 1 + redshift a t₀ t = a t₀ / a t := by simp [redshift]
    rw [h1] at hh
    have : deriv a t = hubble a t * a t := by
      simp only [hubble]; field_simp
    rw [this, hh]; simp only [hg]; ring

/-- Smoothness is redundant in `Aviles.flatLCDM_coeffs`: the flat ΛCDM law makes the scale factor
smooth (bootstrap `contDiffAt_of_law`). -/
theorem flatLCDM_coeffs_r2 : dropped% Checked.Cosmography.Aviles.flatLCDM_coeffs 2 := by
  intro Ω a t₀ hL
  exact flatLCDM_coeffs Ω a t₀ hL (by exact_mod_cast contDiffAt_of_flatLCDM hL 6)

theorem F1_l0_r2 : dropped% Checked.Records.F1_l0 2 := by
  intro a t₀ hL
  exact Checked.Records.F1_l0 a t₀ hL (by exact_mod_cast contDiffAt_of_flatLCDM hL 6)

theorem F3_D4_LCDM_r2 : dropped% Checked.Records.F3_D4_LCDM 2 := by
  intro a t₀ hL
  exact Checked.Records.F3_D4_LCDM a t₀ hL (by exact_mod_cast contDiffAt_of_flatLCDM hL 6)

/-- A flat CPL expansion law makes the scale factor smooth at `t₀` (every finite order). -/
theorem contDiffAt_of_flatCPL {Ω w₀ wₐ : ℝ} {a : ℝ → ℝ} {t₀ : ℝ} (hL : CPL.IsFlatCPL Ω w₀ wₐ a t₀)
    (n : ℕ) : ContDiffAt ℝ n a t₀ := by
  obtain ⟨-, hev⟩ := hL
  have ha0 : 0 < a t₀ := hev.self_of_nhds.1
  set H := hubble a t₀
  set g : ℝ → ℝ := fun x => Ω * (a t₀ / x) ^ 3 + (1 - Ω) * (a t₀ / x) ^ (3 * (1 + w₀ + wₐ)) *
    Real.exp (-(3 * wₐ * (a t₀ / x - 1)) / (a t₀ / x)) with hg
  refine contDiffAt_of_law n a (fun x => x * H * √(g x)) t₀ ?_ ?_
  · have hu : ContinuousAt (fun x : ℝ => a t₀ / x) (a t₀) :=
      continuousAt_const.div continuousAt_id ha0.ne'
    have hu1 : (fun x : ℝ => a t₀ / x) (a t₀) = 1 := div_self ha0.ne'
    have hgc : ContinuousAt g (a t₀) := by
      simp only [hg]
      refine ((hu.pow 3).const_mul Ω).add (((hu.rpow_const (Or.inl (div_self ha0.ne' ▸ one_ne_zero))).const_mul
        (1 - Ω)).mul (Real.continuous_exp.continuousAt.comp ?_))
      exact ((hu.sub continuousAt_const).const_mul (3 * wₐ)).neg.div hu (by rw [div_self ha0.ne']; norm_num)
    have hg1 : g (a t₀) = 1 := by
      simp only [hg, div_self ha0.ne']; norm_num
    have hne : ∀ᶠ x in 𝓝 (a t₀), g x ≠ 0 := hgc.eventually_ne (by rw [hg1]; norm_num)
    have hpos : ∀ᶠ x in 𝓝 (a t₀), 0 < x := lt_mem_nhds ha0
    filter_upwards [hne, hpos] with x hx hx0
    have hus : ContDiffAt ℝ n (fun x : ℝ => a t₀ / x) x := contDiffAt_const.div contDiffAt_id hx0.ne'
    have hupos : a t₀ / x ≠ 0 := (div_pos ha0 hx0).ne'
    have hgs : ContDiffAt ℝ n g x := by
      simp only [hg]
      exact ((hus.pow 3).const_smul Ω).add (((hus.rpow_const_of_ne hupos).const_smul (1 - Ω)).mul
        ((((hus.sub contDiffAt_const).const_smul (3 * wₐ)).neg.div hus hupos).exp))
    exact (contDiffAt_id.mul contDiffAt_const).mul (hgs.sqrt hx)
  · filter_upwards [hev] with t ⟨hpos, hdt, hh⟩
    refine ⟨hdt, ?_⟩
    have h1 : 1 + redshift a t₀ t = a t₀ / a t := by simp [redshift]
    have h2 : redshift a t₀ t = a t₀ / a t - 1 := by simp [redshift]
    rw [h1, h2] at hh
    have : deriv a t = hubble a t * a t := by
      simp only [hubble]; field_simp
    rw [this, hh]; simp only [hg]; ring

theorem flatCPL_coeffs_r2 : dropped% Checked.Cosmography.CPL.flatCPL_coeffs 2 := by
  intro Ω w₀ wₐ a t₀ hL
  exact CPL.flatCPL_coeffs Ω w₀ wₐ a t₀ hL (by exact_mod_cast contDiffAt_of_flatCPL hL 5)

theorem printedL0_ne_r2 : dropped% Checked.Cosmography.CPL.printedL0_ne 2 := by
  intro Ω w₀ wₐ a t₀ hL hne
  exact CPL.printedL0_ne Ω w₀ wₐ a t₀ hL (by exact_mod_cast contDiffAt_of_flatCPL hL 5) hne

theorem F2_toy_r2 : dropped% Checked.Records.F2_toy 2 := by
  intro a t₀ hL
  exact Checked.Records.F2_toy a t₀ hL (by exact_mod_cast contDiffAt_of_flatCPL hL 5)

theorem F2_error_r2 : dropped% Checked.Records.F2_error 2 := by
  intro w₀ a t₀ hL
  exact Checked.Records.F2_error w₀ a t₀ hL (by exact_mod_cast contDiffAt_of_flatCPL hL 5)

/-! ### The separation pair: a toy profile -/

noncomputable def toyP (η : ℝ) : ℝ := 1 - (1 + η ^ 2) * Real.exp (-η ^ 2)
noncomputable def toyQ (η : ℝ) : ℝ := 2 * η ^ 3 * Real.exp (-η ^ 2)
noncomputable def toyQ' (η : ℝ) : ℝ := (6 * η ^ 2 - 4 * η ^ 4) * Real.exp (-η ^ 2)

theorem toy_hasDerivAt_exp (η : ℝ) :
    HasDerivAt (fun η : ℝ => Real.exp (-η ^ 2)) (-(2 * η) * Real.exp (-η ^ 2)) η := by
  have := ((hasDerivAt_pow 2 η).neg).exp
  convert this using 1; simp only [Pi.neg_apply]; push_cast; ring

theorem toyP_deriv (η : ℝ) : HasDerivAt toyP (toyQ η) η := by
  have h := ((hasDerivAt_pow 2 η).const_add 1).mul (toy_hasDerivAt_exp η)
  have := h.const_sub 1
  unfold toyP toyQ
  convert this using 1; push_cast; ring

theorem toyQ_deriv (η : ℝ) : HasDerivAt toyQ (toyQ' η) η := by
  have h := ((hasDerivAt_pow 3 η).const_mul 2).mul (toy_hasDerivAt_exp η)
  unfold toyQ toyQ'
  convert h using 1; push_cast; ring

theorem toyP_zero : toyP 0 = 0 := by simp [toyP]
theorem toyQ_zero : toyQ 0 = 0 := by simp [toyQ]

theorem toyQ_pos : ∀ η ∈ Ioi (0 : ℝ), 0 < toyQ η := by
  intro η hη; unfold toyQ; have : (0 : ℝ) < η := hη; positivity

theorem toyP_lim : Tendsto toyP atTop (𝓝 1) := by
  have hu : Tendsto (fun η : ℝ => η ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
  have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hu
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hu
  have := (h0.add h1).const_sub 1
  simp only [add_zero, sub_zero] at this
  refine this.congr fun η => ?_
  simp only [Function.comp, toyP, pow_zero, pow_one]; ring

theorem toy_decay : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - toyP η) ≤ toyQ η := by
  intro M
  filter_upwards [eventually_ge_atTop (|M| + 1)] with η hη
  have h1 : (1 : ℝ) ≤ η := by linarith [abs_nonneg M]
  have hM : |M| ≤ η := by linarith
  have he := Real.exp_pos (-η ^ 2)
  have key : M * (1 + η ^ 2) ≤ 2 * η ^ 3 := by
    calc M * (1 + η ^ 2) ≤ |M| * (1 + η ^ 2) := by
          apply mul_le_mul_of_nonneg_right (le_abs_self M); positivity
      _ ≤ η * (2 * η ^ 2) := by
          apply mul_le_mul hM (by nlinarith) (by positivity) (by linarith)
      _ = 2 * η ^ 3 := by ring
  have : 1 - toyP η = (1 + η ^ 2) * Real.exp (-η ^ 2) := by unfold toyP; ring
  rw [this]; unfold toyQ
  nlinarith [mul_le_mul_of_nonneg_right key he.le]

/-- `f = ∫₀^η p`, so that `f' = p` and `f(0) = 0`. -/
noncomputable def toyF (η : ℝ) : ℝ := ∫ s in (0 : ℝ)..η, toyP s

theorem toyP_cont : Continuous toyP := by unfold toyP; fun_prop

theorem toyF_deriv (η : ℝ) : HasDerivAt toyF (toyP η) η :=
  (toyP_cont.integral_hasStrictDerivAt 0 η).hasDerivAt

/-- `f` chosen so that `q' = −f q` (the Falkner–Skan equation with `β = 0`), `f = −q'/q`, `f(0) = 0`. -/
noncomputable def toyG (η : ℝ) : ℝ := if η = 0 then 0 else -(toyQ' η / toyQ η)

theorem toyG_ode (η : ℝ) (hη : η ∈ Ici (0 : ℝ)) :
    toyQ' η = -(toyG η * toyQ η) - 0 * (1 - toyP η ^ 2) := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ η from hη) with h | h
  · subst h; simp [toyQ', toyG]
  · have hq := toyQ_pos η h
    simp only [toyG, h.ne', ite_false]
    field_simp
    ring

open Checked.FalknerSkan in
/-- `f' = p` is needed for the first profile in `fs_separation_equal`: the toy profile with `f = −q'/q`
satisfies `q' = −f q` (`β = 0`), every boundary and decay condition, but `0` is not the separation value. -/
theorem fs_separation_equal_h1 : necessity% Checked.FalknerSkan.SeparationEqual.fs_separation_equal 1 := by
  obtain ⟨β, hβ, f, p, q, hf, hp, hq, hf0, hp0, hq0, hlim, hpos, hdec⟩ :=
    Separation.fs_separation_exists
  refine ⟨0, β, toyG, toyP, toyQ, f, p, q, fun η _ => (toyP_deriv η).hasDerivWithinAt,
    fun η hη => by rw [← toyG_ode η hη]; exact (toyQ_deriv η).hasDerivWithinAt, by simp [toyG],
    toyP_zero, toyQ_zero, toyP_lim, toyQ_pos, toy_decay, hf, hp, hq, hf0, hp0, hq0, hlim, hpos, hdec, ?_⟩
  intro h; have := hβ.2; linarith

open Checked.FalknerSkan in
theorem fs_separation_equal_h10 : necessity% Checked.FalknerSkan.SeparationEqual.fs_separation_equal 10 := by
  obtain ⟨β, hβ, f, p, q, hf, hp, hq, hf0, hp0, hq0, hlim, hpos, hdec⟩ :=
    Separation.fs_separation_exists
  refine ⟨β, 0, f, p, q, toyG, toyP, toyQ, hf, hp, hq, hf0, hp0, hq0, hlim, hpos, hdec,
    fun η _ => (toyP_deriv η).hasDerivWithinAt,
    fun η hη => by rw [← toyG_ode η hη]; exact (toyQ_deriv η).hasDerivWithinAt, by simp [toyG],
    toyP_zero, toyQ_zero, toyP_lim, toyQ_pos, toy_decay, ?_⟩
  intro h; have := hβ.2; linarith

open Checked.FalknerSkan in
/-- The Falkner–Skan equation is needed for the first profile in `fs_separation_equal`: the toy
profile with `f = ∫ p` meets every other condition at `β = 0`, which is not the separation value. -/
theorem fs_separation_equal_h3 : necessity% Checked.FalknerSkan.SeparationEqual.fs_separation_equal 3 := by
  obtain ⟨β, hβ, f, p, q, hf, hp, hq, hf0, hp0, hq0, hlim, hpos, hdec⟩ :=
    Separation.fs_separation_exists
  refine ⟨0, β, toyF, toyP, toyQ, f, p, q, fun η _ => (toyF_deriv η).hasDerivWithinAt,
    fun η _ => (toyP_deriv η).hasDerivWithinAt, by simp [toyF],
    toyP_zero, toyQ_zero, toyP_lim, toyQ_pos, toy_decay, hf, hp, hq, hf0, hp0, hq0, hlim, hpos, hdec, ?_⟩
  intro h; have := hβ.2; linarith

open Checked.FalknerSkan in
theorem fs_separation_equal_h12 : necessity% Checked.FalknerSkan.SeparationEqual.fs_separation_equal 12 := by
  obtain ⟨β, hβ, f, p, q, hf, hp, hq, hf0, hp0, hq0, hlim, hpos, hdec⟩ :=
    Separation.fs_separation_exists
  refine ⟨β, 0, f, p, q, toyF, toyP, toyQ, hf, hp, hq, hf0, hp0, hq0, hlim, hpos, hdec,
    fun η _ => (toyF_deriv η).hasDerivWithinAt,
    fun η _ => (toyP_deriv η).hasDerivWithinAt, by simp [toyF],
    toyP_zero, toyQ_zero, toyP_lim, toyQ_pos, toy_decay, ?_⟩
  intro h; have := hβ.2; linarith

/-! ### Smoothness in the distance series: comparison of `kink n` with `1 + t` -/

theorem kink_pt (n : ℕ) (s : ℝ) (hs : |s| ≤ 1 / 4) :
    1 / 2 ≤ kink n s ∧ abs (s ^ (n + 1) * |s|) = |s| ^ (n + 2) := by
  have he : abs (s ^ (n + 1) * |s|) = |s| ^ (n + 2) := by
    rw [abs_mul, abs_abs, abs_pow]; ring
  refine ⟨?_, he⟩
  have h1 : |s| ^ (n + 1) ≤ 1 := pow_le_one₀ (abs_nonneg s) (by linarith)
  have hn : abs (s ^ (n + 1) * |s|) ≤ |s| := by rw [he, pow_succ]; nlinarith [abs_nonneg s]
  have hg := abs_le.1 hn
  have hs' := abs_le.1 hs
  unfold kink; nlinarith [abs_nonneg s]

theorem cub0_pt (s : ℝ) (hs : |s| ≤ 1 / 4) : 1 / 2 ≤ cub 0 s := by
  have := abs_le.1 hs; simp [cub]; linarith

theorem near0 : ∀ᶠ t in 𝓝 (0 : ℝ), |t| ≤ 1 / 4 := by
  have : Iic (1 / 4 : ℝ) ∈ 𝓝 |(0 : ℝ)| := Iic_mem_nhds (by norm_num)
  exact continuous_abs.continuousAt.preimage_mem_nhds this

/-- `|1/a − 1/b| ≤ 4|s|ⁿ⁺²` for `a = kink n`, `b = 1 + t`, `|s| ≤ 1/4`. -/
theorem inv_diff (n : ℕ) (s : ℝ) (hs : |s| ≤ 1 / 4) :
    |1 / kink n s - 1 / cub 0 s| ≤ 4 * |s| ^ (n + 2) := by
  obtain ⟨ha, he⟩ := kink_pt n s hs
  have hb := cub0_pt s hs
  have hab : 1 / kink n s - 1 / cub 0 s = -(s ^ (n + 1) * |s|) / (kink n s * cub 0 s) := by
    field_simp; simp only [kink, cub]; ring
  have : 1 / 4 ≤ kink n s * cub 0 s := by nlinarith
  have hp : 0 < kink n s * cub 0 s := by linarith
  rw [hab, abs_div, abs_neg, he, abs_of_pos hp, div_le_iff₀ hp]
  nlinarith [pow_nonneg (abs_nonneg s) (n + 2)]

theorem kink_inv_cont (n : ℕ) (t : ℝ) (ht : |t| ≤ 1 / 4) :
    ContinuousOn (fun s => 1 / kink n s) (uIcc t 0) := by
  apply ContinuousOn.div continuousOn_const (kink_cont n).continuousOn
  intro s hs
  have : |s| ≤ |t| := by
    rcases le_total t 0 with h | h
    · rw [uIcc_of_le h] at hs; rw [abs_of_nonpos hs.2, abs_of_nonpos h]; linarith [hs.1]
    · rw [uIcc_of_ge h] at hs; rw [abs_of_nonneg hs.1, abs_of_nonneg h]; linarith [hs.2]
  linarith [(kink_pt n s (by linarith)).1]

theorem cub0_inv_cont (t : ℝ) (ht : |t| ≤ 1 / 4) :
    ContinuousOn (fun s => 1 / cub 0 s) (uIcc t 0) := by
  apply ContinuousOn.div continuousOn_const (by unfold cub; fun_prop)
  intro s hs
  have : |s| ≤ |t| := by
    rcases le_total t 0 with h | h
    · rw [uIcc_of_le h] at hs; rw [abs_of_nonpos hs.2, abs_of_nonpos h]; linarith [hs.1]
    · rw [uIcc_of_ge h] at hs; rw [abs_of_nonneg hs.1, abs_of_nonneg h]; linarith [hs.2]
  linarith [cub0_pt s (by linarith)]

theorem abs_le_of_uIcc {t s : ℝ} (hs : s ∈ uIcc t 0) : |s| ≤ |t| := by
  rcases le_total t 0 with h | h
  · rw [uIcc_of_le h] at hs; rw [abs_of_nonpos hs.2, abs_of_nonpos h]; linarith [hs.1]
  · rw [uIcc_of_ge h] at hs; rw [abs_of_nonneg hs.1, abs_of_nonneg h]; linarith [hs.2]

/-- The comoving distances of `kink n` and `1 + t` differ by at most `4|t|ⁿ⁺³`, and that of `kink n`
is at most `2|t|`. -/
theorem comoving_bounds (n : ℕ) (t : ℝ) (ht : |t| ≤ 1 / 4) :
    |BambaY.comoving (kink n) 0 t - BambaY.comoving (cub 0) 0 t| ≤ 4 * |t| ^ (n + 3) ∧
    |BambaY.comoving (kink n) 0 t| ≤ 2 * |t| := by
  have hia : IntervalIntegrable (fun s => 1 / kink n s) MeasureTheory.volume t 0 :=
    (kink_inv_cont n t ht).intervalIntegrable
  have hib : IntervalIntegrable (fun s => 1 / cub 0 s) MeasureTheory.volume t 0 :=
    (cub0_inv_cont t ht).intervalIntegrable
  constructor
  · unfold BambaY.comoving
    rw [← intervalIntegral.integral_sub hia hib]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t) (b := 0)
      (f := fun s => 1 / kink n s - 1 / cub 0 s) (C := 4 * |t| ^ (n + 2)) (fun s hs => by
        have hs' := abs_le_of_uIcc (uIoc_subset_uIcc hs)
        rw [Real.norm_eq_abs]
        calc _ ≤ 4 * |s| ^ (n + 2) := inv_diff n s (by linarith)
          _ ≤ 4 * |t| ^ (n + 2) := by gcongr)
    rw [Real.norm_eq_abs, zero_sub, abs_neg] at this
    calc _ ≤ 4 * |t| ^ (n + 2) * |t| := this
      _ = 4 * |t| ^ (n + 3) := by ring
  · unfold BambaY.comoving
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t) (b := 0)
      (f := fun s => 1 / kink n s) (C := 2) (fun s hs => by
        have hs' := abs_le_of_uIcc (uIoc_subset_uIcc hs)
        have hk := (kink_pt n s (by linarith)).1
        rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_iff₀ (by linarith)]
        linarith)
    rw [Real.norm_eq_abs, zero_sub, abs_neg] at this
    exact this

/-- `tⁿ⁺¹|t|` is not `o(tⁿ⁺²)`. -/
theorem pabs_not_littleO (n : ℕ) :
    ¬ (fun t : ℝ => t ^ (n + 1) * |t|) =o[𝓝 0] (fun t => t ^ (n + 2)) := by
  intro h
  have h1 := h.def (show (0 : ℝ) < 1 / 2 by norm_num)
  have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), t = 0 := by
    filter_upwards [h1] with t ht
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_abs] at ht
    have : |t| ^ (n + 2) = 0 := by
      apply le_antisymm _ (by positivity)
      have e : |t| ^ (n + 1) * |t| = |t| ^ (n + 2) := by ring
      linarith
    simpa using this
  have hne : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0 := self_mem_nhdsWithin
  have := (h2.filter_mono nhdsWithin_le_nhds).and hne
  exact (this.exists).elim fun t ht => ht.2 ht.1

/-- **Decomposition argument.** If `R = E + tⁿ⁺¹|t| W` with `E = o(tⁿ⁺²)` and `W → 1`, and `|Y| ≤ 4|t|`,
then `R` is not `o(Yⁿ⁺²)`. -/
theorem not_littleO_decomp (n : ℕ) (R Y E W : ℝ → ℝ) (hY : ∀ᶠ t in 𝓝 0, |Y t| ≤ 4 * |t|)
    (hE : E =o[𝓝 0] fun t => t ^ (n + 2)) (hW : Tendsto W (𝓝 0) (𝓝 1))
    (hR : ∀ᶠ t in 𝓝 0, R t = E t + t ^ (n + 1) * |t| * W t) :
    ¬ R =o[𝓝 0] fun t => Y t ^ (n + 2) := by
  intro h
  have hYO : (fun t => Y t ^ (n + 2)) =O[𝓝 0] fun t => t ^ (n + 2) := by
    refine Asymptotics.IsBigO.of_bound (4 ^ (n + 2)) ?_
    filter_upwards [hY] with t ht
    simp only [Real.norm_eq_abs, abs_pow]
    calc |Y t| ^ (n + 2) ≤ (4 * |t|) ^ (n + 2) := pow_le_pow_left₀ (abs_nonneg _) ht _
      _ = 4 ^ (n + 2) * |t| ^ (n + 2) := by ring
  have hRo := h.trans_isBigO hYO
  have hgW : (fun t => t ^ (n + 1) * |t| * W t) =o[𝓝 0] fun t => t ^ (n + 2) :=
    (hRo.sub hE).congr' (by filter_upwards [hR] with t ht; rw [ht]; ring) EventuallyEq.rfl
  have hWinv : Tendsto (fun t => (W t)⁻¹) (𝓝 0) (𝓝 1) := by simpa using hW.inv₀ one_ne_zero
  have hb : (fun t => (W t)⁻¹) =O[𝓝 0] fun _ => (1 : ℝ) := hWinv.isBigO_one ℝ
  have hW0 : ∀ᶠ t in 𝓝 (0 : ℝ), W t ≠ 0 := hW.eventually_ne one_ne_zero
  apply pabs_not_littleO n
  refine ((hgW.mul_isBigO hb).congr' ?_ ?_)
  · filter_upwards [hW0] with t ht; field_simp
  · exact Eventually.of_forall fun t => by simp

theorem yred_one {a : ℝ → ℝ} (h0 : a 0 = 1) {t : ℝ} (ht : a t ≠ 0) :
    BambaY.yred a 0 t = 1 - a t := by
  simp only [BambaY.yred, redshift, h0]; field_simp; ring

theorem kink1_d2 : deriv (deriv (kink 1)) = fun x : ℝ => 6 * |x| := by
  rw [kink_deriv]; funext x; apply HasDerivAt.deriv
  have := ((pabs_hasDerivAt 0 x).const_mul ((1 : ℕ) + 2 : ℝ)).const_add 1
  convert this using 1; push_cast; ring

theorem kink1_coeffs : decel (kink 1) 0 = 0 ∧ cosmoCoeff 3 (kink 1) 0 = 0 := by
  have i3 : iteratedDeriv 3 (kink 1) 0 = 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, kink1_d2,
      deriv_const_mul_field']; simp [deriv_abs_zero]
  refine ⟨?_, ?_⟩
  · rw [decel, kink1_d2]; simp
  · simp [cosmoCoeff, i3]

/-- Smoothness (`C³`) is needed in `BambaY.lumDist_y_third_order`: `a = 1 + t + t²|t|` is `C²`, its
junk third derivative gives `j₀ = 0`, the same coefficients as `1 + t`, and the two remainders differ by
`t²|t| (1 + o(1)) + O(|t|⁴)`. -/
theorem lumDist_y_third_order_h1 : necessity% Checked.Cosmography.BambaY.lumDist_y_third_order 1 := by
  refine ⟨kink 1, 0, kink_ne 1, by rw [kink_hubble]; norm_num, ?_⟩
  have hb := BambaY.lumDist_y_third_order (cub 0) 0 (cub_smooth 0 _) (cub_ne 0)
    (by rw [cub_hubble]; norm_num)
  obtain ⟨hq, hj⟩ := kink1_coeffs
  set ya := fun t => BambaY.yred (kink 1) 0 t
  set yb := fun t => BambaY.yred (cub 0) 0 t
  have hyb : ∀ t, |t| ≤ 1 / 4 → yb t = -t := fun t ht => by
    simp only [yb]; rw [yred_one (by simp [cub]) (by linarith [cub0_pt t ht])]; simp [cub]
  have hya : ∀ t, |t| ≤ 1 / 4 → ya t = -t - t ^ 2 * |t| := fun t ht => by
    simp only [ya]; rw [yred_one (by simp [kink]) (by linarith [(kink_pt 1 t ht).1])]; simp only [kink]; ring
  set W := fun t => 1 + 3 / 2 * (ya t + yb t) + 11 / 6 * (ya t ^ 2 + ya t * yb t + yb t ^ 2)
  set Δ := fun t => BambaY.lumDistFlat (kink 1) 0 t - BambaY.lumDistFlat (cub 0) 0 t
  -- `E = R_b + Δ`
  apply not_littleO_decomp 1 _ ya (fun t => BambaY.remainderY BambaY.correctD2y (cub 0) 0 t + Δ t) W
  · filter_upwards [near0] with t ht
    rw [hya t ht]
    have he := (kink_pt 1 t ht).2
    have h3 : |t| ^ (1 + 2) ≤ |t| := by
      have : |t| ^ (1 + 2) = |t| * |t| ^ 2 := by ring
      rw [this]; have : |t| ^ 2 ≤ 1 := by nlinarith [abs_nonneg t]
      nlinarith [abs_nonneg t]
    calc abs (-t - t ^ 2 * |t|) ≤ |-t| + abs (t ^ 2 * |t|) := abs_sub _ _
      _ = |t| + |t| ^ (1 + 2) := by rw [abs_neg, ← he]
      _ ≤ 4 * |t| := by linarith [abs_nonneg t]
  · refine IsLittleO.add ?_ ?_
    · refine hb.trans_isBigO (Asymptotics.IsBigO.of_bound 1 ?_)
      filter_upwards [near0] with t ht
      simp only [yb] at hyb
      rw [hyb t ht]; simp
    · refine Asymptotics.IsBigO.trans_isLittleO (g := fun t => |t| ^ (1 + 3)) ?_ ?_
      · refine Asymptotics.IsBigO.of_bound 16 ?_
        filter_upwards [near0] with t ht
        obtain ⟨hc, hca⟩ := comoving_bounds 1 t ht
        have hk := (kink_pt 1 t ht).1
        have hb' := cub0_pt t ht
        have hid := inv_diff 1 t ht
        simp only [Δ, BambaY.lumDistFlat, redshift, Real.norm_eq_abs, abs_pow, abs_abs]
        have e1 : kink 1 0 = 1 := by simp [kink]
        have e2 : cub 0 0 = 1 := by simp [cub]
        rw [e1, e2]
        have : 1 * (1 + (1 / kink 1 t - 1)) * BambaY.comoving (kink 1) 0 t -
            1 * (1 + (1 / cub 0 t - 1)) * BambaY.comoving (cub 0) 0 t =
            (1 / kink 1 t - 1 / cub 0 t) * BambaY.comoving (kink 1) 0 t +
            1 / cub 0 t * (BambaY.comoving (kink 1) 0 t - BambaY.comoving (cub 0) 0 t) := by ring
        rw [this]
        have hinvb : |1 / cub 0 t| ≤ 2 := by
          rw [abs_of_pos (by positivity), div_le_iff₀ (by linarith)]; linarith
        calc _ ≤ |(1 / kink 1 t - 1 / cub 0 t) * BambaY.comoving (kink 1) 0 t| +
              |1 / cub 0 t * (BambaY.comoving (kink 1) 0 t - BambaY.comoving (cub 0) 0 t)| :=
              abs_add_le _ _
          _ ≤ 4 * |t| ^ (1 + 2) * (2 * |t|) + 2 * (4 * |t| ^ (1 + 3)) := by
              rw [abs_mul, abs_mul]
              gcongr
          _ = 16 * |t| ^ (1 + 3) := by ring
      · refine Asymptotics.IsLittleO.of_bound fun c hc => ?_
        have hlt : ∀ᶠ t in 𝓝 (0 : ℝ), |t| ≤ c := by
          have : Iic c ∈ 𝓝 |(0 : ℝ)| := Iic_mem_nhds (by simpa using hc)
          exact continuous_abs.continuousAt.preimage_mem_nhds this
        filter_upwards [hlt] with t ht
        simp only [Real.norm_eq_abs, abs_pow, abs_abs]
        calc |t| ^ (1 + 3) = |t| * |t| ^ (1 + 2) := by ring
          _ ≤ c * |t| ^ (1 + 2) := by gcongr
  · have hya0 : Tendsto ya (𝓝 0) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => -t - t ^ 2 * |t|) (𝓝 0) (𝓝 0) :=
        (by fun_prop : Continuous fun t : ℝ => -t - t ^ 2 * |t|).tendsto' 0 0 (by simp)
      exact this.congr' (by filter_upwards [near0] with t ht; rw [hya t ht])
    have hyb0 : Tendsto yb (𝓝 0) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := continuous_neg.tendsto' 0 0 (by simp)
      exact this.congr' (by filter_upwards [near0] with t ht; rw [hyb t ht])
    have := ((hya0.add hyb0).const_mul (3 / 2)).const_add 1 |>.add
      (((hya0.pow 2).add (hya0.mul hyb0)).add (hyb0.pow 2) |>.const_mul (11 / 6))
    simpa [W] using this
  · filter_upwards [near0] with t ht
    have hyat := hya t ht
    have hybt := hyb t ht
    simp only [ya, yb] at hyat hybt
    simp only [BambaY.remainderY, BambaY.seriesY, BambaY.correctD2y, BambaY.D1y, Δ, W, ya, yb, hq, hj,
      cub_decel, cub_j, kink_hubble, cub_hubble, hyat, hybt]
    ring

/-! ### Fifth order, generic comparison -/

theorem lumflat_bound (n : ℕ) (t : ℝ) (ht : |t| ≤ 1 / 4) :
    |BambaY.lumDistFlat (kink n) 0 t - BambaY.lumDistFlat (cub 0) 0 t| ≤ 16 * |t| ^ (n + 3) := by
  obtain ⟨hc, hca⟩ := comoving_bounds n t ht
  have hb' := cub0_pt t ht
  have hid := inv_diff n t ht
  have e1 : kink n 0 = 1 := by simp [kink]
  have e2 : cub 0 0 = 1 := by simp [cub]
  simp only [BambaY.lumDistFlat, redshift, e1, e2]
  have : 1 * (1 + (1 / kink n t - 1)) * BambaY.comoving (kink n) 0 t -
      1 * (1 + (1 / cub 0 t - 1)) * BambaY.comoving (cub 0) 0 t =
      (1 / kink n t - 1 / cub 0 t) * BambaY.comoving (kink n) 0 t +
      1 / cub 0 t * (BambaY.comoving (kink n) 0 t - BambaY.comoving (cub 0) 0 t) := by ring
  rw [this]
  have hinvb : |1 / cub 0 t| ≤ 2 := by
    rw [abs_of_pos (by positivity), div_le_iff₀ (by linarith)]; linarith
  calc _ ≤ |(1 / kink n t - 1 / cub 0 t) * BambaY.comoving (kink n) 0 t| +
        |1 / cub 0 t * (BambaY.comoving (kink n) 0 t - BambaY.comoving (cub 0) 0 t)| := abs_add_le _ _
    _ ≤ 4 * |t| ^ (n + 2) * (2 * |t|) + 2 * (4 * |t| ^ (n + 3)) := by
        rw [abs_mul, abs_mul]; gcongr
    _ = 16 * |t| ^ (n + 3) := by ring

theorem lumDist_flat (a : ℝ → ℝ) (t : ℝ) :
    BambaK.lumDist 0 a 0 t = BambaY.lumDistFlat a 0 t := by
  simp [BambaK.lumDist, BambaY.lumDistFlat, Transverse.transverse]

theorem angDist_eq (n : ℕ) (t : ℝ) (ht : |t| ≤ 1 / 4) :
    BambaA.angDist 0 (kink n) 0 t = kink n t * BambaY.comoving (kink n) 0 t := by
  have hk := (kink_pt n t ht).1
  have e1 : kink n 0 = 1 := by simp [kink]
  simp only [BambaA.angDist, lumDist_flat, BambaY.lumDistFlat, redshift, e1]
  field_simp; ring

theorem angDist_eq_cub (t : ℝ) (ht : |t| ≤ 1 / 4) :
    BambaA.angDist 0 (cub 0) 0 t = cub 0 t * BambaY.comoving (cub 0) 0 t := by
  have hk := cub0_pt t ht
  have e1 : cub 0 0 = 1 := by simp [cub]
  simp only [BambaA.angDist, lumDist_flat, BambaY.lumDistFlat, redshift, e1]
  field_simp; ring

theorem angflat_bound (n : ℕ) (t : ℝ) (ht : |t| ≤ 1 / 4) :
    |BambaA.angDist 0 (kink n) 0 t - BambaA.angDist 0 (cub 0) 0 t| ≤ 16 * |t| ^ (n + 3) := by
  obtain ⟨hc, hca⟩ := comoving_bounds n t ht
  obtain ⟨hk, he⟩ := kink_pt n t ht
  have hb' : |cub 0 t| ≤ 2 := by have := abs_le.1 ht; simp [cub]; rw [abs_le]; constructor <;> linarith
  rw [angDist_eq n t ht, angDist_eq_cub t ht]
  have hab : kink n t - cub 0 t = t ^ (n + 1) * |t| := by simp [kink, cub]
  have : kink n t * BambaY.comoving (kink n) 0 t - cub 0 t * BambaY.comoving (cub 0) 0 t =
      (kink n t - cub 0 t) * BambaY.comoving (kink n) 0 t +
      cub 0 t * (BambaY.comoving (kink n) 0 t - BambaY.comoving (cub 0) 0 t) := by ring
  rw [this, hab]
  calc _ ≤ |t ^ (n + 1) * |t| * BambaY.comoving (kink n) 0 t| +
        |cub 0 t * (BambaY.comoving (kink n) 0 t - BambaY.comoving (cub 0) 0 t)| := abs_add_le _ _
    _ ≤ |t| ^ (n + 2) * (2 * |t|) + 2 * (4 * |t| ^ (n + 3)) := by
        rw [abs_mul (t ^ (n + 1) * |t|), abs_mul (cub 0 t), he]; gcongr
    _ ≤ 16 * |t| ^ (n + 3) := by
        have : 0 ≤ |t| ^ (n + 3) := by positivity
        have e : |t| ^ (n + 2) * (2 * |t|) = 2 * |t| ^ (n + 3) := by ring
        linarith

theorem cub0_coeffs : decel (cub 0) 0 = 0 ∧ cosmoCoeff 3 (cub 0) 0 = 0 ∧
    cosmoCoeff 4 (cub 0) 0 = 0 ∧ cosmoCoeff 5 (cub 0) 0 = 0 := by
  have i4 : iteratedDeriv 4 (cub 0) 0 = 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, cub_d3]; simp
  have i5 : iteratedDeriv 5 (cub 0) 0 = 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
      iteratedDeriv_one, cub_d3]; simp
  refine ⟨cub_decel 0, by rw [cub_j]; ring, ?_, ?_⟩ <;> simp [cosmoCoeff, i4, i5]

theorem bigO_bound_littleO (n : ℕ) (C : ℝ) (Δ : ℝ → ℝ)
    (h : ∀ᶠ t in 𝓝 (0 : ℝ), |Δ t| ≤ C * |t| ^ (n + 3)) : Δ =o[𝓝 0] fun t => t ^ (n + 2) := by
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun t => |t| ^ (n + 3)) ?_ ?_
  · refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [h] with t ht
    simpa [Real.norm_eq_abs, abs_pow, abs_abs] using ht
  · refine Asymptotics.IsLittleO.of_bound fun c hc => ?_
    have hlt : ∀ᶠ t in 𝓝 (0 : ℝ), |t| ≤ c := by
      have : Iic c ∈ 𝓝 |(0 : ℝ)| := Iic_mem_nhds (by simpa using hc)
      exact continuous_abs.continuousAt.preimage_mem_nhds this
    filter_upwards [hlt] with t ht
    simp only [Real.norm_eq_abs, abs_pow, abs_abs]
    calc |t| ^ (n + 3) = |t| * |t| ^ (n + 2) := by ring
      _ ≤ c * |t| ^ (n + 2) := by gcongr

theorem tendsto_of_abs_le {Y : ℝ → ℝ} (h : ∀ᶠ t in 𝓝 (0 : ℝ), |Y t| ≤ 4 * |t|) :
    Tendsto Y (𝓝 0) (𝓝 0) := by
  have h4 : Tendsto (fun t : ℝ => 4 * |t|) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs.tendsto (0 : ℝ)).const_mul 4
  refine squeeze_zero_norm' ?_ h4
  filter_upwards [h] with t ht
  simpa [Real.norm_eq_abs] using ht

/-- **Generic comparison.** Two remainders `Rₐ = Dₐ − S(Yₐ)`, `R_b = D_b − S(Y_b)` with the same
series `S(Y) = Y(1 + c₁Y + c₂Y² + c₃Y³ + c₄Y⁴)`; `R_b = o(Y_bⁿ⁺²)`, `Dₐ − D_b = O(|t|ⁿ⁺³)`, and
`Yₐ − Y_b = −tⁿ⁺¹|t| V` with `V → 1`: then `Rₐ` is not `o(Yₐⁿ⁺²)`. -/
theorem compare_general (n : ℕ) (Ra Rb Da Db Ya Yb V : ℝ → ℝ) (c1 c2 c3 c4 C : ℝ)
    (hRa : ∀ᶠ t in 𝓝 (0 : ℝ), Ra t = Da t - Ya t * (1 + c1 * Ya t + c2 * Ya t ^ 2 + c3 * Ya t ^ 3
      + c4 * Ya t ^ 4))
    (hRb : ∀ᶠ t in 𝓝 (0 : ℝ), Rb t = Db t - Yb t * (1 + c1 * Yb t + c2 * Yb t ^ 2 + c3 * Yb t ^ 3
      + c4 * Yb t ^ 4))
    (hb : Rb =o[𝓝 0] fun t => Yb t ^ (n + 2))
    (hD : ∀ᶠ t in 𝓝 (0 : ℝ), |Da t - Db t| ≤ C * |t| ^ (n + 3))
    (hYa : ∀ᶠ t in 𝓝 (0 : ℝ), |Ya t| ≤ 4 * |t|) (hYb : ∀ᶠ t in 𝓝 (0 : ℝ), |Yb t| ≤ 4 * |t|)
    (hdiff : ∀ᶠ t in 𝓝 (0 : ℝ), Ya t - Yb t = -(t ^ (n + 1) * |t| * V t))
    (hV : Tendsto V (𝓝 0) (𝓝 1)) :
    ¬ Ra =o[𝓝 0] fun t => Ya t ^ (n + 2) := by
  set W : ℝ → ℝ := fun t => 1 + c1 * (Ya t + Yb t) + c2 * (Ya t ^ 2 + Ya t * Yb t + Yb t ^ 2)
    + c3 * (Ya t ^ 3 + Ya t ^ 2 * Yb t + Ya t * Yb t ^ 2 + Yb t ^ 3)
    + c4 * (Ya t ^ 4 + Ya t ^ 3 * Yb t + Ya t ^ 2 * Yb t ^ 2 + Ya t * Yb t ^ 3 + Yb t ^ 4) with hW
  have ha0 := tendsto_of_abs_le hYa
  have hb0 := tendsto_of_abs_le hYb
  have hW1 : Tendsto W (𝓝 0) (𝓝 1) := by
    have := ((((tendsto_const_nhds (x := (1 : ℝ))).add ((ha0.add hb0).const_mul c1)).add
      ((((ha0.pow 2).add (ha0.mul hb0)).add (hb0.pow 2)).const_mul c2)).add
      ((((((ha0.pow 3).add ((ha0.pow 2).mul hb0)).add (ha0.mul (hb0.pow 2))).add (hb0.pow 3))).const_mul c3)).add
      (((((((ha0.pow 4).add ((ha0.pow 3).mul hb0)).add ((ha0.pow 2).mul (hb0.pow 2))).add
        (ha0.mul (hb0.pow 3))).add (hb0.pow 4))).const_mul c4)
    simpa [hW] using this
  have hBO : (fun t => Yb t ^ (n + 2)) =O[𝓝 0] fun t => t ^ (n + 2) := by
    refine Asymptotics.IsBigO.of_bound (4 ^ (n + 2)) ?_
    filter_upwards [hYb] with t ht
    simp only [Real.norm_eq_abs, abs_pow]
    calc |Yb t| ^ (n + 2) ≤ (4 * |t|) ^ (n + 2) := pow_le_pow_left₀ (abs_nonneg _) ht _
      _ = 4 ^ (n + 2) * |t| ^ (n + 2) := by ring
  apply not_littleO_decomp n Ra Ya (fun t => Rb t + (Da t - Db t)) (fun t => V t * W t) hYa
  · exact (hb.trans_isBigO hBO).add (bigO_bound_littleO n C _ hD)
  · simpa using hV.mul hW1
  · filter_upwards [hRa, hRb, hdiff] with t h1 h2 h3
    have hYa' : Ya t = Yb t - t ^ (n + 1) * |t| * V t := by linarith
    rw [h1, h2, hYa']; simp only [hW]; rw [hYa']; ring

theorem yb_cub (t : ℝ) (ht : |t| ≤ 1 / 4) : BambaY.yred (cub 0) 0 t = -t := by
  rw [yred_one (by simp [cub]) (by linarith [cub0_pt t ht])]; simp [cub]

theorem ya_kink (n : ℕ) (t : ℝ) (ht : |t| ≤ 1 / 4) :
    BambaY.yred (kink n) 0 t = -t - t ^ (n + 1) * |t| := by
  rw [yred_one (by simp [kink]) (by linarith [(kink_pt n t ht).1])]; simp only [kink]; ring

theorem ya_bound (n : ℕ) : ∀ᶠ t in 𝓝 (0 : ℝ), |BambaY.yred (kink n) 0 t| ≤ 4 * |t| := by
  filter_upwards [near0] with t ht
  rw [ya_kink n t ht]
  have he := (kink_pt n t ht).2
  have h3 : |t| ^ (n + 2) ≤ |t| := by
    have : |t| ^ (n + 2) = |t| * |t| ^ (n + 1) := by ring
    rw [this]; have : |t| ^ (n + 1) ≤ 1 := pow_le_one₀ (abs_nonneg t) (by linarith)
    nlinarith [abs_nonneg t]
  calc abs (-t - t ^ (n + 1) * |t|) ≤ |-t| + abs (t ^ (n + 1) * |t|) := abs_sub _ _
    _ = |t| + |t| ^ (n + 2) := by rw [abs_neg, he]
    _ ≤ 4 * |t| := by linarith [abs_nonneg t]

theorem yb_bound : ∀ᶠ t in 𝓝 (0 : ℝ), |BambaY.yred (cub 0) 0 t| ≤ 4 * |t| := by
  filter_upwards [near0] with t ht
  rw [yb_cub t ht, abs_neg]; linarith [abs_nonneg t]

theorem y_diff (n : ℕ) : ∀ᶠ t in 𝓝 (0 : ℝ),
    BambaY.yred (kink n) 0 t - BambaY.yred (cub 0) 0 t = -(t ^ (n + 1) * |t| * (fun _ => (1 : ℝ)) t) := by
  filter_upwards [near0] with t ht
  rw [ya_kink n t ht, yb_cub t ht]; ring

/-- Smoothness (`C⁵`) is needed in `BambaK.lumDist_y_fifth_order` (flat case `K = 0`). -/
theorem lumDist_y_fifth_order_h1 : necessity% Checked.Cosmography.BambaK.lumDist_y_fifth_order 1 := by
  refine ⟨0, kink 3, 0, kink_ne 3, by rw [kink_hubble]; norm_num, ?_⟩
  obtain ⟨hq, hj, hs, hl⟩ := kink3_coeffs
  obtain ⟨bq, bj, bs, bl⟩ := cub0_coeffs
  refine compare_general 3 _ (fun t => BambaK.remK BambaY.correctD2y BambaK.correctD3y BambaK.correctD4y 0
      (cub 0) 0 t) (fun t => BambaK.lumDist 0 (kink 3) 0 t) (fun t => BambaK.lumDist 0 (cub 0) 0 t)
    _ _ (fun _ => 1) (BambaY.D1y 0) (BambaY.correctD2y 0 0 1) (BambaK.correctD3y 0 0 0 1)
    (BambaK.correctD4y 0 0 0 0 1) 16 ?_ ?_
    (BambaK.lumDist_y_fifth_order 0 (cub 0) 0 (cub_smooth 0 _) (cub_ne 0) (by rw [cub_hubble]; norm_num))
    ?_ (ya_bound 3) yb_bound (y_diff 3) tendsto_const_nhds
  · exact Eventually.of_forall fun t => by
      simp only [BambaK.remK, BambaK.seriesY4, hq, hj, hs, hl, omega0_flat, kink_hubble]; ring
  · exact Eventually.of_forall fun t => by
      simp only [BambaK.remK, BambaK.seriesY4, bq, bj, bs, bl, omega0_flat, cub_hubble]; ring
  · filter_upwards [near0] with t ht
    rw [lumDist_flat, lumDist_flat]; exact lumflat_bound 3 t ht

/-- Smoothness (`C⁵`) is needed in `BambaA.angDist_y_fifth_order` (flat case `K = 0`). -/
theorem angDist_y_fifth_order_h1 : necessity% Checked.Cosmography.BambaA.angDist_y_fifth_order 1 := by
  refine ⟨0, kink 3, 0, kink_ne 3, by rw [kink_hubble]; norm_num, ?_⟩
  obtain ⟨hq, hj, hs, hl⟩ := kink3_coeffs
  obtain ⟨bq, bj, bs, bl⟩ := cub0_coeffs
  refine compare_general 3 _ (fun t => BambaA.remA BambaA.correctDA3 BambaA.correctDA4 0 (cub 0) 0 t)
    (fun t => BambaA.angDist 0 (kink 3) 0 t) (fun t => BambaA.angDist 0 (cub 0) 0 t)
    _ _ (fun _ => 1) (BambaA.DA1 0) (BambaA.DA2 0 0 1) (BambaA.correctDA3 0 0 0 1)
    (BambaA.correctDA4 0 0 0 0 1) 16 ?_ ?_
    (BambaA.angDist_y_fifth_order 0 (cub 0) 0 (cub_smooth 0 _) (cub_ne 0) (by rw [cub_hubble]; norm_num))
    ?_ (ya_bound 3) yb_bound (y_diff 3) tendsto_const_nhds
  · exact Eventually.of_forall fun t => by
      simp only [BambaA.remA, hq, hj, hs, hl, omega0_flat, kink_hubble]; ring
  · exact Eventually.of_forall fun t => by
      simp only [BambaA.remA, bq, bj, bs, bl, omega0_flat, cub_hubble]; ring
  · filter_upwards [near0] with t ht
    exact angflat_bound 3 t ht

theorem z_diff (n : ℕ) : ∀ᶠ t in 𝓝 (0 : ℝ),
    redshift (kink n) 0 t - redshift (cub 0) 0 t =
      -(t ^ (n + 1) * |t| * (fun t => 1 / (kink n t * cub 0 t)) t) := by
  filter_upwards [near0] with t ht
  have hk := (kink_pt n t ht).1
  have hb := cub0_pt t ht
  have e1 : kink n 0 = 1 := by simp [kink]
  have e2 : cub 0 0 = 1 := by simp [cub]
  simp only [redshift, e1, e2]
  have : kink n t ≠ 0 := by linarith
  have : cub 0 t ≠ 0 := by linarith
  field_simp; simp only [kink, cub]; ring

theorem z_V (n : ℕ) : Tendsto (fun t => 1 / (kink n t * cub 0 t)) (𝓝 0) (𝓝 1) := by
  have hc : Continuous (fun t => kink n t * cub 0 t) := (kink_cont n).mul (by unfold cub; fun_prop)
  have h := (hc.tendsto 0).inv₀ (by simp [kink, cub])
  simpa [kink, cub] using h

theorem zb_bound : ∀ᶠ t in 𝓝 (0 : ℝ), |redshift (cub 0) 0 t| ≤ 4 * |t| := by
  filter_upwards [near0] with t ht
  have hb := cub0_pt t ht
  have hp : 0 < cub 0 t := by linarith
  have e : redshift (cub 0) 0 t = -t / cub 0 t := by
    rw [redshift, eq_div_iff hp.ne']
    have e0 : cub 0 0 = 1 := by simp [cub]
    rw [e0]; field_simp; simp only [cub]; ring
  rw [e, abs_div, abs_neg, abs_of_pos hp, div_le_iff₀ hp]
  nlinarith [abs_nonneg t]

theorem za_bound (n : ℕ) : ∀ᶠ t in 𝓝 (0 : ℝ), |redshift (kink n) 0 t| ≤ 4 * |t| := by
  filter_upwards [kink_bounds n] with t ht using ht.2

/-- Smoothness (`C⁵`) is needed in `BambaZ.lumDist_z_fifth_order` (flat case `K = 0`). -/
theorem lumDist_z_fifth_order_h1 : necessity% Checked.Cosmography.BambaZ.lumDist_z_fifth_order 1 := by
  refine ⟨0, kink 3, 0, kink_ne 3, by rw [kink_hubble]; norm_num, ?_⟩
  obtain ⟨hq, hj, hs, hl⟩ := kink3_coeffs
  obtain ⟨bq, bj, bs, bl⟩ := cub0_coeffs
  refine compare_general 3 _ (fun t => BambaZ.remLz BambaZ.correctDL4z 0 (cub 0) 0 t)
    (fun t => BambaK.lumDist 0 (kink 3) 0 t) (fun t => BambaK.lumDist 0 (cub 0) 0 t)
    _ _ _ (BambaZ.DL1z 0) (BambaZ.DL2z 0 0 0) (BambaZ.DL3z 0 0 0 0)
    (BambaZ.correctDL4z 0 0 0 0 0) 16 ?_ ?_
    (BambaZ.lumDist_z_fifth_order 0 (cub 0) 0 (cub_smooth 0 _) (cub_ne 0) (by rw [cub_hubble]; norm_num))
    ?_ (za_bound 3) zb_bound (z_diff 3) (z_V 3)
  · exact Eventually.of_forall fun t => by
      simp only [BambaZ.remLz, BambaZ.seriesZ, hq, hj, hs, hl, curvK_flat, kink_hubble]; ring
  · exact Eventually.of_forall fun t => by
      simp only [BambaZ.remLz, BambaZ.seriesZ, bq, bj, bs, bl, curvK_flat, cub_hubble]; ring
  · filter_upwards [near0] with t ht
    rw [lumDist_flat, lumDist_flat]; exact lumflat_bound 3 t ht

/-- Smoothness (`C⁵`) is needed in `BambaZ.angDist_z_fifth_order` (flat case `K = 0`). -/
theorem angDist_z_fifth_order_h1 : necessity% Checked.Cosmography.BambaZ.angDist_z_fifth_order 1 := by
  refine ⟨0, kink 3, 0, kink_ne 3, by rw [kink_hubble]; norm_num, ?_⟩
  obtain ⟨hq, hj, hs, hl⟩ := kink3_coeffs
  obtain ⟨bq, bj, bs, bl⟩ := cub0_coeffs
  refine compare_general 3 _ (fun t => BambaZ.remAz BambaZ.correctDA4z 0 (cub 0) 0 t)
    (fun t => BambaA.angDist 0 (kink 3) 0 t) (fun t => BambaA.angDist 0 (cub 0) 0 t)
    _ _ _ (BambaZ.DA1z 0) (BambaZ.DA2z 0 0 0) (BambaZ.DA3z 0 0 0 0)
    (BambaZ.correctDA4z 0 0 0 0 0) 16 ?_ ?_
    (BambaZ.angDist_z_fifth_order 0 (cub 0) 0 (cub_smooth 0 _) (cub_ne 0) (by rw [cub_hubble]; norm_num))
    ?_ (za_bound 3) zb_bound (z_diff 3) (z_V 3)
  · exact Eventually.of_forall fun t => by
      simp only [BambaZ.remAz, BambaZ.seriesZ, hq, hj, hs, hl, curvK_flat, kink_hubble]; ring
  · exact Eventually.of_forall fun t => by
      simp only [BambaZ.remAz, BambaZ.seriesZ, bq, bj, bs, bl, curvK_flat, cub_hubble]; ring
  · filter_upwards [near0] with t ht
    exact angflat_bound 3 t ht

theorem dQ_eq {a : ℝ → ℝ} (h0 : a 0 = 1) {t : ℝ} (ht : 0 < a t) :
    CVdQ.dQFlat a 0 t = √(a t) * BambaY.comoving a 0 t := by
  have e : 1 + redshift a 0 t = (a t)⁻¹ := by simp [redshift, h0]
  have hi : 0 < (a t)⁻¹ := inv_pos.2 ht
  have hr : (a t)⁻¹ ^ ((3 : ℝ) / 2) = (a t)⁻¹ * (√(a t))⁻¹ := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hi, Real.rpow_one,
      ← Real.sqrt_eq_rpow, Real.sqrt_inv]
  have hs : 0 < √(a t) := Real.sqrt_pos.2 ht
  simp only [CVdQ.dQFlat, BambaY.lumDistFlat, e, h0, hr]
  field_simp

theorem sqrt_diff {a b : ℝ} (ha : 1 / 2 ≤ a) (hb : 1 / 2 ≤ b) : |√a - √b| ≤ |a - b| := by
  have sa := Real.sq_sqrt (show 0 ≤ a by linarith)
  have sb := Real.sq_sqrt (show 0 ≤ b by linarith)
  have h1 : 1 / 2 ≤ √a := by
    rw [show (1 / 2 : ℝ) = √(1 / 4) by rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have h2 : 1 / 2 ≤ √b := by
    rw [show (1 / 2 : ℝ) = √(1 / 4) by rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hab : a - b = (√a - √b) * (√a + √b) := by nlinarith
  rw [hab, abs_mul, abs_of_pos (show 0 < √a + √b by linarith)]
  have := abs_nonneg (√a - √b)
  nlinarith

theorem dQflat_bound (n : ℕ) (t : ℝ) (ht : |t| ≤ 1 / 4) :
    |CVdQ.dQFlat (kink n) 0 t - CVdQ.dQFlat (cub 0) 0 t| ≤ 16 * |t| ^ (n + 3) := by
  obtain ⟨hc, hca⟩ := comoving_bounds n t ht
  obtain ⟨hk, he⟩ := kink_pt n t ht
  have hb := cub0_pt t ht
  rw [dQ_eq (by simp [kink]) (by linarith), dQ_eq (by simp [cub]) (by linarith)]
  have hsd := sqrt_diff hk hb
  have hab : kink n t - cub 0 t = t ^ (n + 1) * |t| := by simp [kink, cub]
  rw [hab, he] at hsd
  have hsb : |√(cub 0 t)| ≤ 2 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    have := abs_le.1 ht
    calc √(cub 0 t) ≤ √4 := Real.sqrt_le_sqrt (by simp [cub]; linarith)
      _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have : √(kink n t) * BambaY.comoving (kink n) 0 t - √(cub 0 t) * BambaY.comoving (cub 0) 0 t =
      (√(kink n t) - √(cub 0 t)) * BambaY.comoving (kink n) 0 t +
      √(cub 0 t) * (BambaY.comoving (kink n) 0 t - BambaY.comoving (cub 0) 0 t) := by ring
  rw [this]
  calc _ ≤ |(√(kink n t) - √(cub 0 t)) * BambaY.comoving (kink n) 0 t| +
        |√(cub 0 t) * (BambaY.comoving (kink n) 0 t - BambaY.comoving (cub 0) 0 t)| := abs_add_le _ _
    _ ≤ |t| ^ (n + 2) * (2 * |t|) + 2 * (4 * |t| ^ (n + 3)) := by
        rw [abs_mul (√(kink n t) - √(cub 0 t)), abs_mul (√(cub 0 t))]; gcongr
    _ ≤ 16 * |t| ^ (n + 3) := by
        have : 0 ≤ |t| ^ (n + 3) := by positivity
        have e : |t| ^ (n + 2) * (2 * |t|) = 2 * |t| ^ (n + 3) := by ring
        linarith

/-- Smoothness (`C³`) is needed in `CVdQ.dQ_y_third_order`: `a = 1 + t + t²|t|` against `1 + t`. -/
theorem dQ_y_third_order_h1 : necessity% Checked.Cosmography.CVdQ.dQ_y_third_order 1 := by
  refine ⟨kink 1, 0, kink_ne 1, by rw [kink_hubble]; norm_num, ?_⟩
  obtain ⟨hq, hj⟩ := kink1_coeffs
  obtain ⟨bq, bj, -, -⟩ := cub0_coeffs
  refine compare_general 1 _ (fun t => CVdQ.remainderQ CVdQ.correctQ2 (cub 0) 0 t)
    (fun t => CVdQ.dQFlat (kink 1) 0 t) (fun t => CVdQ.dQFlat (cub 0) 0 t)
    _ _ (fun _ => 1) (-(0 : ℝ) / 2) (CVdQ.correctQ2 0 0 1) 0 0 16 ?_ ?_
    (CVdQ.dQ_y_third_order (cub 0) 0 (cub_smooth 0 _) (cub_ne 0) (by rw [cub_hubble]; norm_num))
    ?_ (ya_bound 1) yb_bound (y_diff 1) tendsto_const_nhds
  · exact Eventually.of_forall fun t => by
      simp only [CVdQ.remainderQ, CVdQ.seriesQ, hq, hj, kink_hubble]; ring
  · exact Eventually.of_forall fun t => by
      simp only [CVdQ.remainderQ, CVdQ.seriesQ, bq, bj, cub_hubble]; ring
  · filter_upwards [near0] with t ht
    exact dQflat_bound 1 t ht

/-! ### `f(R)` slow-roll ratios: the range `0 < Ω < 1` (`FREta.eta20_hasDerivAt`, `FREta.eta30_hasDerivAt`) -/

/-- A function with `f(0) = 0` and `εᵏ f(ε) → G(0) ≠ 0` (for `ε ≠ 0`) has no derivative at `0`. -/
theorem not_hasDerivAt_of (f G : ℝ → ℝ) (k : ℕ) (hG : ContinuousAt G 0) (hG0 : G 0 ≠ 0)
    (hf0 : f 0 = 0) (hfg : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), ε ^ k * f ε = G ε) (c : ℝ) :
    ¬ HasDerivAt f c 0 := by
  intro h
  have hc : Tendsto f (𝓝 0) (𝓝 0) := by simpa [hf0] using h.continuousAt.tendsto
  have h1 : Tendsto (fun ε : ℝ => ε ^ k * f ε) (𝓝[≠] 0) (𝓝 0) := by
    have := ((continuous_pow k).tendsto (0 : ℝ)).mul hc
    simpa using this.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto G (𝓝[≠] 0) (𝓝 (G 0)) := hG.tendsto.mono_left nhdsWithin_le_nhds
  exact hG0 (tendsto_nhds_unique (h1.congr' hfg) h2).symm

theorem eta_ne : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), ε ≠ 0 := self_mem_nhdsWithin

theorem poly_ne (P : ℝ → ℝ) (hP : Continuous P) (h0 : P 0 ≠ 0) : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), P ε ≠ 0 :=
  (hP.continuousAt.eventually_ne h0).filter_mono nhdsWithin_le_nhds

/-- `0 < Ω` is needed in `FREta.eta20_hasDerivAt`: at `Ω = 0` the family's denominator has a double zero
at `ε = 0`, `η₂₀(0, ε) → 26/3348 ≠ 0` while `η₂₀(0, 0) = 0` (Lean's `x/0 = 0`), so there is no derivative. -/
theorem eta20_hasDerivAt_h1 : necessity% Checked.Cosmography.FREta.eta20_hasDerivAt 1 := by
  refine ⟨0, by norm_num, fun h => ?_⟩
  set P : ℝ → ℝ := fun ε => 3 * ε ^ 3 + 7 * ε ^ 2 + 33 * ε + 93
  refine not_hasDerivAt_of (FREta.eta20 0) (fun ε => -2 * (3 * ε - 13) / (36 * P ε)) 0
    (by apply ContinuousAt.div (by fun_prop) (by fun_prop); simp [P]) (by simp [P]) h.1 ?_ _ h.2
  filter_upwards [eta_ne, poly_ne P (by fun_prop) (by simp [P])] with ε he hp
  have hD : FREta.Dfam 0 ε = -(ε ^ 2 * P ε) := by
    simp only [P]; unfold FREta.Dfam FRCosmo.P0 FRCosmo.Q0 FREta.qL FREta.jL FREta.sL FREta.lL; ring
  rw [FREta.eta20_eq]; beta_reduce; rw [hD]
  simp only [pow_zero, one_mul, FREta.N2e]
  field_simp
  ring

/-- `Ω < 1` is needed in `FREta.eta20_hasDerivAt`: at `Ω = 2` the denominator has a simple zero at
`ε = 0`, `η₂₀(2, ε) → −186/34992 ≠ 0` while `η₂₀(2, 0) = 0`. -/
theorem eta20_hasDerivAt_h2 : necessity% Checked.Cosmography.FREta.eta20_hasDerivAt 2 := by
  refine ⟨2, by norm_num, fun h => ?_⟩
  set P : ℝ → ℝ := fun ε => 24 * ε ^ 4 + 149 * ε ^ 3 + 361 * ε ^ 2 + 453 * ε + 243
  refine not_hasDerivAt_of (FREta.eta20 2) (fun ε => FREta.N2e 2 ε / (144 * P ε)) 0
    (by apply ContinuousAt.div (by unfold FREta.N2e; fun_prop) (by fun_prop); simp [P])
    (by simp [P, FREta.N2e]; norm_num) h.1 ?_ _ h.2
  filter_upwards [eta_ne, poly_ne P (by fun_prop) (by simp [P])] with ε he hp
  have hD : FREta.Dfam 2 ε = 4 * ε * P ε := by
    simp only [P]; unfold FREta.Dfam FRCosmo.P0 FRCosmo.Q0 FREta.qL FREta.jL FREta.sL FREta.lL; ring
  rw [FREta.eta20_eq]; beta_reduce; rw [hD]
  simp only [pow_zero, one_mul]
  field_simp
  ring

/-- `0 < Ω` is needed in `FREta.eta30_hasDerivAt`: at `Ω = 0`, `ε η₃₀(0, ε) → 1/20088 ≠ 0`, so `η₃₀(0, ·)`
is unbounded near `0` while `η₃₀(0, 0) = 0`. -/
theorem eta30_hasDerivAt_h1 : necessity% Checked.Cosmography.FREta.eta30_hasDerivAt 1 := by
  refine ⟨0, by norm_num, fun h => ?_⟩
  set P : ℝ → ℝ := fun ε => 3 * ε ^ 3 + 7 * ε ^ 2 + 33 * ε + 93
  refine not_hasDerivAt_of (FREta.eta30 0) (fun ε => (13 * ε + 1) / (216 * P ε)) 1
    (by apply ContinuousAt.div (by fun_prop) (by fun_prop); simp [P]) (by simp [P]) h.1 ?_ _ h.2
  filter_upwards [eta_ne, poly_ne P (by fun_prop) (by simp [P])] with ε he hp
  have hD : FREta.Dfam 0 ε = -(ε ^ 2 * P ε) := by
    simp only [P]; unfold FREta.Dfam FRCosmo.P0 FRCosmo.Q0 FREta.qL FREta.jL FREta.sL FREta.lL; ring
  have hJ : FREta.Jfam 0 ε = 2 * ε := by unfold FREta.Jfam FREta.qL FREta.jL; ring
  rw [FREta.eta30_eq]; beta_reduce; rw [hD, hJ]
  simp only [pow_one, FREta.N3e]
  field_simp
  ring

/-- `Ω < 1` is needed in `FREta.eta30_hasDerivAt`: at `Ω = 2`, `η₃₀(2, ε) → 282/(−629856) ≠ 0` while
`η₃₀(2, 0) = 0`. -/
theorem eta30_hasDerivAt_h2 : necessity% Checked.Cosmography.FREta.eta30_hasDerivAt 2 := by
  refine ⟨2, by norm_num, fun h => ?_⟩
  set P : ℝ → ℝ := fun ε => 24 * ε ^ 4 + 149 * ε ^ 3 + 361 * ε ^ 2 + 453 * ε + 243
  refine not_hasDerivAt_of (FREta.eta30 2) (fun ε => FREta.N3e 2 ε / (864 * (-(ε + 3)) * P ε)) 0
    (by apply ContinuousAt.div (by unfold FREta.N3e; fun_prop) (by fun_prop); simp [P])
    (by simp [P, FREta.N3e]; norm_num) h.1 ?_ _ h.2
  filter_upwards [eta_ne, poly_ne P (by fun_prop) (by simp [P]),
    poly_ne (fun ε => -(ε + 3)) (by fun_prop) (by norm_num)] with ε he hp hj
  have hD : FREta.Dfam 2 ε = 4 * ε * P ε := by
    simp only [P]; unfold FREta.Dfam FRCosmo.P0 FRCosmo.Q0 FREta.qL FREta.jL FREta.sL FREta.lL; ring
  have hJ : FREta.Jfam 2 ε = -(ε + 3) := by unfold FREta.Jfam FREta.qL FREta.jL; ring
  rw [FREta.eta30_eq]; beta_reduce; rw [hD, hJ]
  simp only [pow_zero, one_mul]
  field_simp
  ring

/-! ### Local existence of a scale factor for an expansion law -/

/-- Smoothness of the expansion law is needed in `CPLExistence.exists_local_model`: for
`E(x) = 1 + |x − 1|` no `C⁵` scale factor with `a(0) = 1` solves `ȧ = a E(a)` near `0` (it would make
`|a − 1| = ȧ/a − 1` differentiable at `0`, so `o(t)` at its minimum, while `a − 1 = t + o(t)`). -/
theorem exists_local_model_h1 :
    necessity% Checked.Cosmography.CPLExistence.exists_local_model 1 := by
  refine ⟨fun x => 1 + |x - 1|, ?_⟩
  rintro ⟨a, ha0, hs, hev⟩
  have hd1 : HasDerivAt a 1 0 := by
    have := (hev.self_of_nhds).2; simpa [ha0] using this
  have hda : ∀ᶠ t in 𝓝 (0 : ℝ), deriv a t = a t * (1 + |a t - 1|) :=
    hev.mono fun t ht => ht.2.deriv
  have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < a t := hev.mono fun t ht => ht.1
  have h2d : ContDiffAt ℝ 4 (deriv a) 0 := hs.derivWithin (by norm_num)
  have hD : DifferentiableAt ℝ (fun t => deriv a t / a t - 1) 0 :=
    ((h2d.differentiableAt (by norm_num)).div hd1.differentiableAt (by rw [ha0]; norm_num)).sub_const 1
  have heq : (fun t => deriv a t / a t - 1) =ᶠ[𝓝 0] fun t => |a t - 1| := by
    filter_upwards [hda, hpos] with t h1 h2
    rw [h1]; field_simp; ring
  have hh : DifferentiableAt ℝ (fun t => |a t - 1|) 0 := hD.congr_of_eventuallyEq heq.symm
  have hmin : IsLocalMin (fun t => |a t - 1|) 0 :=
    Eventually.of_forall fun t => by simp [ha0]
  have hz : HasDerivAt (fun t => |a t - 1|) 0 0 := by
    exact hh.hasDerivAt.congr_deriv (hmin.hasDerivAt_eq_zero hh.hasDerivAt)
  have ho := hz.isLittleO
  have hoa := hd1.isLittleO
  have h1 := ho.def (show (0 : ℝ) < 1 / 4 by norm_num)
  have h2 := hoa.def (show (0 : ℝ) < 1 / 4 by norm_num)
  have h3 : ∀ᶠ t in 𝓝 (0 : ℝ), t = 0 := by
    filter_upwards [h1, h2] with t ht1 ht2
    simp only [ha0, sub_self, abs_zero, smul_eq_mul, mul_zero, sub_zero, zero_add,
      Real.norm_eq_abs, mul_one, abs_abs] at ht1 ht2
    have : |t| ≤ |a t - 1| + |a t - 1 - t| := by
      calc |t| = |(a t - 1) - (a t - 1 - t)| := by ring_nf
        _ ≤ |a t - 1| + |a t - 1 - t| := abs_sub _ _
    have : |t| ≤ 0 := by
      have e : a t - 1 - t = a t - 1 - t := rfl
      linarith [abs_nonneg t]
    exact abs_nonpos_iff.1 this
  have hne : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0 := self_mem_nhdsWithin
  have := (h3.filter_mono nhdsWithin_le_nhds).and hne
  exact (this.exists).elim fun t ht => ht.2 ht.1

/-! ### The critical cubic of the generalized cubic equation of state -/

/-- `−2 < u` is needed in `CubicEOS.critCubic_existsUnique`: at `u = −32/7`, `w = 124/21`
(`1 + u + w = 7/3 > 0`) the cubic is `(x − 2)(x − 3)(x + 2)`, with two roots above `1`. -/
theorem critCubic_existsUnique_h1 :
    necessity% Checked.Chemistry.CubicEOS.critCubic_existsUnique 1 := by
  refine ⟨-32 / 7, 124 / 21, by norm_num, ?_⟩
  rintro ⟨x, -, hx⟩
  have h2 := hx 2 ⟨by norm_num, by unfold Checked.Chemistry.CubicEOS.critCubic; norm_num⟩
  have h3 := hx 3 ⟨by norm_num, by unfold Checked.Chemistry.CubicEOS.critCubic; norm_num⟩
  linarith

/-- `0 < 1 + u + w` is needed in `CubicEOS.critCubic_existsUnique`: at `u = 0`, `w = −1` the cubic is
`(x − 1)³`, with no root above `1`. -/
theorem critCubic_existsUnique_h2 :
    necessity% Checked.Chemistry.CubicEOS.critCubic_existsUnique 2 := by
  refine ⟨0, -1, by norm_num, ?_⟩
  rintro ⟨x, ⟨h1, hx⟩, -⟩
  have e : Checked.Chemistry.CubicEOS.critCubic 0 (-1) x = (x - 1) ^ 3 := by
    unfold Checked.Chemistry.CubicEOS.critCubic; ring
  rw [e] at hx
  have : x - 1 = 0 := pow_eq_zero_iff (by norm_num) |>.1 hx
  linarith

/-- `0 < a` is needed in `CubicEOS.exists_unique_critical`: with `a = 0` (an ideal gas with excluded
volume, `R = b = 1`, `u = w = 0`) the slope `−T/(v − 1)²` never vanishes for `T > 0`. -/
theorem exists_unique_critical_h2 :
    necessity% Checked.Chemistry.CubicEOS.exists_unique_critical 2 := by
  refine ⟨1, 0, 1, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  rintro ⟨p, ⟨hT, hv, hc, -⟩, -⟩
  have hv1 : p.2 - 1 ≠ 0 := by linarith
  have hD : p.2 ^ 2 + 0 * 1 * p.2 + 0 * 1 ^ 2 ≠ 0 := by nlinarith
  have hd := (Checked.Chemistry.CubicEOS.hasDerivAt_P 1 0 1 0 0 p.1 p.2 hv1 hD).deriv
  rw [hd] at hc
  have : (p.2 - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hv1
  field_simp at hc
  have hp : 0 < p.2 := by linarith
  have h4 : 0 < p.1 * (p.2 * (p.2 + 0) + 0) ^ 2 := by positivity
  linarith

/-- `0 < R` is needed in `CubicEOS.exists_unique_critical`: with `R = 0` (`a = b = 1`, `u = w = 0`) the
slope `2/v³` never vanishes for `v > 1`. -/
theorem exists_unique_critical_h1 :
    necessity% Checked.Chemistry.CubicEOS.exists_unique_critical 1 := by
  refine ⟨0, 1, 1, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  rintro ⟨p, ⟨hT, hv, hc, -⟩, -⟩
  have hv1 : p.2 - 1 ≠ 0 := by linarith
  have hp : 0 < p.2 := by linarith
  have hD : p.2 ^ 2 + 0 * 1 * p.2 + 0 * 1 ^ 2 ≠ 0 := by positivity
  have hd := (Checked.Chemistry.CubicEOS.hasDerivAt_P 0 1 1 0 0 p.1 p.2 hv1 hD).deriv
  rw [hd] at hc
  have : (p.2 - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hv1
  field_simp at hc
  nlinarith

/-! ### Printed `l₀`, `m₀` of flat ΛCDM: the conditions that make the misprints matter -/

/-- `0 < Ω` is needed in `AvilesWitness.printedL0_false_at`: at `Ω = 0` the printed and correct `l₀`
agree (both `1`), so the printed formula holds in every flat ΛCDM model. -/
theorem printedL0_false_at_h1 :
    necessity% Checked.Cosmography.AvilesWitness.printedL0_false_at 1 := by
  refine ⟨0, by norm_num, fun a t₀ hL hs => ?_⟩
  rw [(flatLCDM_coeffs 0 a t₀ hL hs).2.2.2.1]; ring

/-- `0 < Ω` is needed in `AvilesWitness.printedM0_false_at`: at `Ω = 0` the printed and correct `m₀`
agree. -/
theorem printedM0_false_at_h1 :
    necessity% Checked.Cosmography.AvilesWitness.printedM0_false_at 1 := by
  refine ⟨0, by norm_num, by norm_num, fun a t₀ hL hs => ?_⟩
  rw [(flatLCDM_coeffs 0 a t₀ hL hs).2.2.2.2]; ring

/-- `3Ω² + 2Ω − 2 ≠ 0` is needed in `AvilesWitness.printedM0_false_at`: at `Ω = (√7 − 1)/3` the printed
and correct `m₀` agree. -/
theorem printedM0_false_at_h3 :
    necessity% Checked.Cosmography.AvilesWitness.printedM0_false_at 3 := by
  have h7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have hlo : 2 < Real.sqrt 7 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hhi : Real.sqrt 7 < 3 := by
    rw [show (3 : ℝ) = Real.sqrt 9 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  refine ⟨(Real.sqrt 7 - 1) / 3, by linarith, by linarith, fun a t₀ hL hs => ?_⟩
  rw [(flatLCDM_coeffs _ a t₀ hL hs).2.2.2.2]
  linear_combination (3 / 4 * (Real.sqrt 7 - 1)) * h7

/-- A flat ΛCDM model exists for every `Ω` (no range condition): integrate `ȧ = a √(Ω a⁻³ + 1 − Ω)`
from `a(0) = 1` (`CPLExistence.exists_local_model`). -/
theorem exists_flatLCDM_any (Ω : ℝ) : ∃ (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM Ω a t₀ := by
  set E : ℝ → ℝ := fun x => √(Ω * (1 / x) ^ 3 + 1 - Ω) with hE
  have hE1 : E 1 = 1 := by simp [hE]
  have hEs : ContDiffAt ℝ 5 E 1 := by
    have hin : ContDiffAt ℝ 5 (fun x : ℝ => Ω * (1 / x) ^ 3 + 1 - Ω) 1 :=
      (((contDiffAt_const.div contDiffAt_id one_ne_zero).pow 3).const_smul Ω |>.add contDiffAt_const).sub
        contDiffAt_const
    exact hin.sqrt (by norm_num)
  obtain ⟨a, ha0, -, hev⟩ := Checked.Cosmography.CPLExistence.exists_local_model E hEs
  have hH : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < a t ∧ DifferentiableAt ℝ a t ∧ hubble a t = E (a t) := by
    filter_upwards [hev] with t ⟨hp, hd⟩
    refine ⟨hp, hd.differentiableAt, ?_⟩
    simp only [hubble, hd.deriv]; field_simp
  have hH0 : hubble a 0 = 1 := by rw [(hH.self_of_nhds).2.2, ha0, hE1]
  refine ⟨a, 0, by rw [hH0]; norm_num, ?_⟩
  filter_upwards [hH] with t ⟨hp, hd, hh⟩
  refine ⟨hp, hd, ?_⟩
  rw [hh, hH0, one_mul]
  simp only [hE, redshift, ha0]
  congr 1
  field_simp
  ring

/-- `Ω < 1` is redundant in `AvilesWitness.printedL0_false_at`: a flat ΛCDM model exists for every `Ω`
(`exists_flatLCDM_any`), and in it the printed `l₀` is wrong whenever `Ω ≠ 0`. -/
theorem printedL0_false_at_r2 :
    dropped% Checked.Cosmography.AvilesWitness.printedL0_false_at 2 := by
  intro Ω h0 h
  obtain ⟨a, t₀, hL⟩ := exists_flatLCDM_any Ω
  have hs : ContDiffAt ℝ 6 a t₀ := by exact_mod_cast contDiffAt_of_flatLCDM hL 6
  have e := h a t₀ hL hs
  rw [(flatLCDM_coeffs Ω a t₀ hL hs).2.2.2.1] at e
  nlinarith [sq_pos_of_pos h0]

/-- `Ω < 1` is redundant in `AvilesWitness.printedM0_false_at`. -/
theorem printedM0_false_at_r2 :
    dropped% Checked.Cosmography.AvilesWitness.printedM0_false_at 2 := by
  intro Ω h0 hr h
  obtain ⟨a, t₀, hL⟩ := exists_flatLCDM_any Ω
  have hs : ContDiffAt ℝ 6 a t₀ := by exact_mod_cast contDiffAt_of_flatLCDM hL 6
  have e := h a t₀ hL hs
  rw [(flatLCDM_coeffs Ω a t₀ hL hs).2.2.2.2] at e
  have : Ω * (3 * Ω ^ 2 + 2 * Ω - 2) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · exact hr h

end Checked.Trust.NCD
