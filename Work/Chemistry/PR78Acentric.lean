import Mathlib
import Checked.Records.Basic
import Checked.Chemistry.CubicEOS
import Checked.Chemistry.Coexistence

/-!
# Chemistry: does the Robinson–Peng 1978 revision of κ(ω) make Peng–Robinson reproduce its own acentric factor? (run 2026-11-05T1828Z)

**Question.** Run 2026-11-05T1228Z certified (`Checked.Chemistry.PRAcentric.pr_omega1_unique`)
that the Peng–Robinson equation P = RT/(v − b) − a(T)/(v² + 2bv − b²) with Soave's temperature
function a(T) = a_c (1 + κ (1 − √(T/T_c)))² and the original 1976 correlation
κ(ω) = 0.37464 + 1.54226 ω − 0.26992 ω², entered at ω = 1, has acentric factor 0.942: the
equation does not reproduce the ω it is fed. Robinson and Peng (1978) replaced the correlation
for ω > 0.491 by κ(ω) = 0.379642 + 1.48503 ω − 0.164423 ω² + 0.016666 ω³. Does the revised
correlation reproduce its input at ω = 1? Floating point
(`runs/2026-11-05T1828Z/scripts/pr78_float.py`) gives 1.00009: yes, to three decimals.

**What is stated here** (program definitions only: `cubicP R a b 2 (-1) T` is the
Peng–Robinson form RT/(v−b) − a/(v² + 2bv − b²); `IsCriticalIsotherm` (pinned),
`IsMaxwellCoexistence` (pinned), `acentric`, `RoundsTo`). The attraction parameter is `ac` on
the critical isotherm and `ac · (1 + κ(1)(1 − √0.7))²` on the isotherm at 0.7 T_c, with κ(1)
written out as the 1978 correlation at ω = 1.
1. `pr78_omega1_unique`: for every R, a_c > 0, b > 0 and every critical point (T_c, v_c > b) of
   that fluid, every Maxwell coexistence state at 0.7 T_c with liquid volume above b has
   p_s/P_c = 0.0100 (4 decimals) and acentric factor 1.000 (3 decimals), P_c the pressure at
   the critical point.
2. `pr78_omega1_exists`: such a coexistence state exists.

Conventions: molar volume v, co-volume b > 0, a_c > 0; `Real.sqrt`; `Real.logb 10` is log₁₀
(inside `acentric`). No sign is assumed for R or T_c.

FROZEN (annex 40, freeze rule) in run 2026-11-05T1828Z before proof work.
-/

namespace Work.Chemistry.PR78Acentric
open Checked.Records Checked.Chemistry.CubicEOS Checked.Chemistry.Coexistence

/-- Peng–Robinson fluid with Soave's temperature function and the Robinson–Peng 1978 κ(ω) at
ω = 1 (attraction a_c at T_c, a_c (1 + κ(1)(1 − √0.7))² at 0.7 T_c): at any critical point
(v_c > b), every Maxwell coexistence state at T = 0.7 T_c with liquid volume above the co-volume
b has pressure 0.0100 times the critical pressure (4 decimals) and acentric factor 1.000
(3 decimals), the input value. -/
theorem pr78_omega1_unique (R ac b Tc vc vl vg ps : ℝ) (hac : 0 < ac) (hb : 0 < b)
    (hvc : b < vc)
    (hc : IsCriticalIsotherm (cubicP R ac b 2 (-1) Tc) vc)
    (hl : b < vl)
    (h : IsMaxwellCoexistence
      (cubicP R (ac * (1 + (0.379642 + 1.48503 * 1 - 0.164423 * 1 ^ 2 + 0.016666 * 1 ^ 3) *
        (1 - Real.sqrt (7 / 10))) ^ 2) b 2 (-1) (7 / 10 * Tc)) vl vg ps) :
    RoundsTo (ps / cubicP R ac b 2 (-1) Tc vc) 0.0100 4 ∧
      RoundsTo (acentric ps (cubicP R ac b 2 (-1) Tc vc)) 1.000 3 := by
  sorry

/-- Peng–Robinson fluid with Soave's temperature function and the Robinson–Peng 1978 κ(ω) at
ω = 1: at any critical point (v_c > b) there is a Maxwell coexistence state at T = 0.7 T_c with
liquid volume above the co-volume b, and its pressure is 0.0100 times the critical pressure
(4 decimals) and its acentric factor 1.000 (3 decimals). -/
theorem pr78_omega1_exists (R ac b Tc vc : ℝ) (hac : 0 < ac) (hb : 0 < b) (hvc : b < vc)
    (hc : IsCriticalIsotherm (cubicP R ac b 2 (-1) Tc) vc) :
    ∃ vl vg ps, b < vl ∧
      IsMaxwellCoexistence
        (cubicP R (ac * (1 + (0.379642 + 1.48503 * 1 - 0.164423 * 1 ^ 2 + 0.016666 * 1 ^ 3) *
          (1 - Real.sqrt (7 / 10))) ^ 2) b 2 (-1) (7 / 10 * Tc)) vl vg ps ∧
      RoundsTo (ps / cubicP R ac b 2 (-1) Tc vc) 0.0100 4 ∧
      RoundsTo (acentric ps (cubicP R ac b 2 (-1) Tc vc)) 1.000 3 := by
  sorry

end Work.Chemistry.PR78Acentric
