import Mathlib
import Checked.Records.Basic
import Checked.Chemistry.CubicEOS

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
  sorry

end Work.Chemistry.Coexistence
