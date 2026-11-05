import Mathlib
import Checked.Records.Basic
import Checked.Chemistry.CubicEOS
import Checked.Chemistry.Coexistence
import Work.Chemistry.PRCore
import Work.Chemistry.PRExists

/-!
# Chemistry (THE RESULT part 5): does Peng–Robinson reproduce its own acentric factor? (run 2026-11-05T1228Z)

**Question.** The Peng–Robinson (1976) equation of state
P = RT/(v − b) − a(T)/(v² + 2bv − b²) with Soave's temperature function
a(T) = a_c (1 + κ (1 − √(T/T_c)))² and the published correlation
κ(ω) = 0.37464 + 1.54226 ω − 0.26992 ω² is the most used cubic equation of state. Pitzer's
acentric factor ω = −log₁₀(p_s(0.7 T_c)/P_c) − 1 is defined from the vapour pressure at
T_r = 0.7. The correlation κ(ω) is meant to make the equation reproduce that vapour pressure, so
a fluid entered with acentric factor ω should come out of the equation with acentric factor ω.
Does it? At ω = 1 (heavy compounds) floating point (run 2026-11-05T1228Z,
`runs/2026-11-05T1228Z/scripts/pr_float.py`) gives 0.9424: the equation's own acentric factor
falls short of the input by about 0.058, i.e. its reduced vapour pressure at T_r = 0.7 is
about 14 % too high.

**What is stated here** (program definitions only: `cubicP R a b 2 (-1) T` is the
Peng–Robinson form RT/(v−b) − a/(v² + 2bv − b²); `IsCriticalIsotherm` (pinned),
`IsMaxwellCoexistence` (pinned), `acentric`, `RoundsTo`). The attraction parameter is `ac` on
the critical isotherm and `ac · (1 + κ(1)(1 − √0.7))²` on the isotherm at 0.7 T_c, with κ(1)
written out as the published correlation at ω = 1.
1. `pr_omega1_unique`: for every R, a_c > 0, b > 0 and every critical point (T_c, v_c > b) of
   that fluid, every Maxwell coexistence state at 0.7 T_c with liquid volume above b has
   p_s/P_c = 0.0114 (4 decimals) and acentric factor 0.942 (3 decimals), P_c the pressure at the
   critical point.
2. `pr_omega1_exists`: such a coexistence state exists.

Conventions: molar volume v, co-volume b > 0, a_c > 0; `Real.sqrt`; `Real.logb 10` is log₁₀
(inside `acentric`). No sign is assumed for R or T_c: the critical-point conditions force
R T_c > 0, which is all that enters.

FROZEN (annex 40, freeze rule) in run 2026-11-05T1228Z before proof work.
-/

namespace Work.Chemistry.PRAcentric
open Checked.Records Checked.Chemistry.CubicEOS Checked.Chemistry.Coexistence

/-- Peng–Robinson fluid with Soave's temperature function and the published κ(ω) at ω = 1
(attraction a_c at T_c, a_c (1 + κ(1)(1 − √0.7))² at 0.7 T_c): at any critical point
(v_c > b), every Maxwell coexistence state at T = 0.7 T_c with liquid volume above the co-volume
b has pressure 0.0114 times the critical pressure (4 decimals) and acentric factor 0.942
(3 decimals), not the input value 1. -/
theorem pr_omega1_unique (R ac b Tc vc vl vg ps : ℝ) (hac : 0 < ac) (hb : 0 < b)
    (hvc : b < vc)
    (hc : IsCriticalIsotherm (cubicP R ac b 2 (-1) Tc) vc)
    (hl : b < vl)
    (h : IsMaxwellCoexistence
      (cubicP R (ac * (1 + (0.37464 + 1.54226 * 1 - 0.26992 * 1 ^ 2) * (1 - Real.sqrt (7 / 10))) ^ 2)
        b 2 (-1) (7 / 10 * Tc)) vl vg ps) :
    RoundsTo (ps / cubicP R ac b 2 (-1) Tc vc) 0.0114 4 ∧
      RoundsTo (acentric ps (cubicP R ac b 2 (-1) Tc vc)) 0.942 3 := by
  -- Proof (run 2026-11-05T1228Z): `Work.Chemistry.PRCore.pr_unique_core` (reduced variables,
  -- certified window of the reduced pressure `Work.Chemistry.PRReduced.window_of_maxwell`,
  -- θ and P_c from the critical point, ω from certified logarithms).
  exact Work.Chemistry.PRCore.pr_unique_core R ac b Tc vc vl vg ps hac hb hvc hc hl h

/-- Peng–Robinson fluid with Soave's temperature function and the published κ(ω) at ω = 1: at
any critical point (v_c > b) there is a Maxwell coexistence state at T = 0.7 T_c with liquid
volume above the co-volume b, and its pressure is 0.0114 times the critical pressure
(4 decimals) and its acentric factor 0.942 (3 decimals). -/
theorem pr_omega1_exists (R ac b Tc vc : ℝ) (hac : 0 < ac) (hb : 0 < b) (hvc : b < vc)
    (hc : IsCriticalIsotherm (cubicP R ac b 2 (-1) Tc) vc) :
    ∃ vl vg ps, b < vl ∧
      IsMaxwellCoexistence
        (cubicP R (ac * (1 + (0.37464 + 1.54226 * 1 - 0.26992 * 1 ^ 2) * (1 - Real.sqrt (7 / 10))) ^ 2)
          b 2 (-1) (7 / 10 * Tc)) vl vg ps ∧
      RoundsTo (ps / cubicP R ac b 2 (-1) Tc vc) 0.0114 4 ∧
      RoundsTo (acentric ps (cubicP R ac b 2 (-1) Tc vc)) 0.942 3 := by
  -- Proof (run 2026-11-05T1228Z): `Work.Chemistry.PRExists.pr_exists_core` (equal maxima of ψ on
  -- the liquid and gas windows by the intermediate value theorem, then the window theorem).
  exact Work.Chemistry.PRExists.pr_exists_core R ac b Tc vc hac hb hvc hc

end Work.Chemistry.PRAcentric
