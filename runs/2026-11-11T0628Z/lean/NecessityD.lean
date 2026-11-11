import Checked.Trust.NonVacuity
import Checked.Cosmography.CCSLookback
import Checked.Cosmography.BambaDLy
import Checked.Cosmography.CVdQ
import Checked.Cosmography.BambaCurved
import Checked.Cosmography.BambaAngular
import Checked.Cosmography.BambaZ
import Checked.Cosmography.DemianskiZ

/-!
# Hypothesis necessity witnesses, fourth batch (trust track T2b, run 2026-11-11T0628Z)

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
-/

open Set Filter Topology Asymptotics
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

end Checked.Trust.NCD
