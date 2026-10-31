import Mathlib
import Checked.Records.Basic
import Checked.Chemistry.CubicEOS
import Work.Chemistry.CoexistenceReduced

/-!
# Chemistry (THE RESULT parts 5 and 1): vapour–liquid coexistence of the van der Waals fluid,
# certified saturation pressure and acentric factor

**Question.** Below the critical temperature a cubic equation of state predicts vapour–liquid
coexistence by Maxwell's equal-area construction: liquid and gas molar volumes v_l < v_g at the
same pressure p_s with ∫_{v_l}^{v_g} P dv = p_s (v_g − v_l) (equivalently equal molar Gibbs
energy). Pitzer's acentric factor ω = −log₁₀(p_s(0.7 T_c)/P_c) − 1 is the input of every
corresponding-states correlation and of the Soave and Peng–Robinson α(T; ω). For the van der
Waals fluid textbooks quote ω ≈ −0.302 from floating-point root finding.

**What is stated here** (van der Waals, `cubicP R a b 0 0`, critical constants
T_c = 8a/(27Rb), P_c = a/(27b²), from `Checked.Chemistry.CubicEOS.vdW_constants`):
1. `vdW_coexistence_exists`: at T = 0.7 T_c there is a Maxwell coexistence state with
   v_l > b, and its pressure satisfies p_s/P_c = 0.20046 (5 decimals) and ω = −0.3020
   (4 decimals).
2. `vdW_coexistence_unique`: every Maxwell coexistence state at T = 0.7 T_c with v_l > b has
   p_s/P_c = 0.20046 (5 decimals) — the saturation pressure is determined, not just one
   solution of the equations.

Conventions: molar volume v, gas constant R > 0, co-volume b > 0, attraction a > 0; the
integral is Mathlib's interval integral; `Real.logb 10` is log₁₀.

FROZEN (annex 40.1) in run 2026-10-31T1228Z before proof work.
-/

namespace Work.Chemistry.Coexistence
open Checked.Records Checked.Chemistry.CubicEOS

/-- Maxwell equal-area coexistence on the isotherm `p` (pressure as a function of molar
volume): liquid volume `vl` below gas volume `vg`, both at pressure `ps`, and the integral of the
isotherm from `vl` to `vg` equals `ps (vg − vl)`. -/
def IsMaxwellCoexistence (p : ℝ → ℝ) (vl vg ps : ℝ) : Prop :=
  vl < vg ∧ p vl = ps ∧ p vg = ps ∧ ∫ v in vl..vg, p v = ps * (vg - vl)

/-- Pitzer's acentric factor from the saturation pressure `ps` at T = 0.7 T_c and the critical
pressure `pc`: ω = −log₁₀(ps/pc) − 1. -/
noncomputable def acentric (ps pc : ℝ) : ℝ := -Real.logb 10 (ps / pc) - 1

/-- van der Waals fluid at 0.7 of its critical temperature: there is a Maxwell coexistence state
(liquid volume above the co-volume b), and its pressure is 0.20046 P_c to five decimals, so the
acentric factor of the van der Waals fluid is −0.3020 to four decimals. -/
theorem vdW_coexistence_exists (R a b : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    ∃ vl vg ps, b < vl ∧
      IsMaxwellCoexistence (cubicP R a b 0 0 (7 / 10 * (8 * a / (27 * R * b)))) vl vg ps ∧
      RoundsTo (ps / (a / (27 * b ^ 2))) 0.20046 5 ∧
      RoundsTo (acentric ps (a / (27 * b ^ 2))) (-0.3020) 4 := by
  sorry

/-- van der Waals fluid at 0.7 of its critical temperature: every Maxwell coexistence state with
liquid volume above the co-volume b has pressure 0.20046 P_c to five decimals (the saturation
pressure is unique to that accuracy). -/
theorem vdW_coexistence_unique (R a b vl vg ps : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)
    (hl : b < vl)
    (h : IsMaxwellCoexistence (cubicP R a b 0 0 (7 / 10 * (8 * a / (27 * R * b)))) vl vg ps) :
    RoundsTo (ps / (a / (27 * b ^ 2))) 0.20046 5 := by
  -- Proof (run 2026-10-31T1428Z): reduce to `x = v/b`, `π = p/P_c` and apply
  -- `Work.Chemistry.CoexistenceReduced.reduced_window`.
  open Work.Chemistry.CoexistenceReduced in
  obtain ⟨hlg, hpl, hpg, hint⟩ := h
  have hb0 : b ≠ 0 := hb.ne'
  have hPc : 0 < a / (27 * b ^ 2) := by positivity
  have hP : ∀ v, b < v → cubicP R a b 0 0 (7 / 10 * (8 * a / (27 * R * b))) v
      = a / (27 * b ^ 2) * g (v / b) := by
    intro v hv
    have h1 : v - b ≠ 0 := by linarith
    have h2 : v ≠ 0 := by linarith
    have h3 : v / b - 1 ≠ 0 := by
      rw [div_sub_one hb0]; exact div_ne_zero h1 hb0
    unfold cubicP g
    rw [div_sub_one hb0]
    field_simp
    ring
  have h1 : 1 < vl / b := by rw [lt_div_iff₀ hb]; linarith
  have h12 : vl / b < vg / b := div_lt_div_of_pos_right hlg hb
  -- the integral in reduced variables
  have hI : ∫ v in vl..vg, cubicP R a b 0 0 (7 / 10 * (8 * a / (27 * R * b))) v
      = a / (27 * b ^ 2) * (b * (ψ 0 (vg / b) - ψ 0 (vl / b))) := by
    rw [intervalIntegral.integral_congr (g := fun v => a / (27 * b ^ 2) * g (v / b))
      (fun v hv => by
        rw [Set.uIcc_of_le hlg.le] at hv
        exact hP v (by linarith [hv.1]))]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div (fun x => g x) hb0]
    congr 1
    rw [smul_eq_mul]
    congr 1
    have hd : ∀ x ∈ Set.uIcc (vl / b) (vg / b), HasDerivAt (ψ 0) (g x - 0) x := by
      intro x hx
      rw [Set.uIcc_of_le h12.le] at hx
      exact hasDerivAt_ψ 0 (by linarith [hx.1])
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((continuousOn_g (t := vg / b) h1).sub continuousOn_const |>.intervalIntegrable_of_Icc h12.le)
    simpa using this
  have hgl : g (vl / b) = ps / (a / (27 * b ^ 2)) := by
    rw [← hpl, hP vl hl]; field_simp
  have hgg : g (vg / b) = ps / (a / (27 * b ^ 2)) := by
    rw [← hpg, hP vg (by linarith)]; field_simp
  have hψ : ψ (ps / (a / (27 * b ^ 2))) (vl / b) = ψ (ps / (a / (27 * b ^ 2))) (vg / b) := by
    rw [hI] at hint
    have e1 := ψ_shift (ps / (a / (27 * b ^ 2))) 0 (vl / b)
    have e2 := ψ_shift (ps / (a / (27 * b ^ 2))) 0 (vg / b)
    have key : ψ 0 (vg / b) - ψ 0 (vl / b) = ps / (a / (27 * b ^ 2)) * (vg / b - vl / b) := by
      have hne : a / (27 * b ^ 2) * b ≠ 0 := by positivity
      apply mul_left_cancel₀ hne
      rw [show a / (27 * b ^ 2) * b * (ψ 0 (vg / b) - ψ 0 (vl / b))
          = a / (27 * b ^ 2) * (b * (ψ 0 (vg / b) - ψ 0 (vl / b))) by ring, hint]
      field_simp
    linarith
  obtain ⟨lo, hi⟩ := reduced_window h1 h12 hgl hgg hψ
  unfold RoundsTo
  rw [abs_le]
  constructor <;> norm_num <;> linarith

end Work.Chemistry.Coexistence
