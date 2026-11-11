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
* **Smoothness under an expansion law is redundant** (`Aviles.flatLCDM_coeffs`, `CPL.flatCPL_coeffs`,
  `CPL.printedL0_ne`, records `F1_l0`, `F2_toy`, `F2_error`, `F3_D4_LCDM`): the flat ΛCDM and CPL laws
  say `ȧ = Φ(a)` near `t₀` with `Φ` smooth near `a(t₀)`, and a bootstrap (`contDiffAt_of_law`: `a` is
  `Cᵏ` ⇒ `ȧ = Φ ∘ a` is `Cᵏ` ⇒ `a` is `Cᵏ⁺¹`) makes `a` smooth at `t₀`.
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

end Checked.Trust.NCD
