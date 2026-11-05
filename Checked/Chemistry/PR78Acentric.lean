import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Checked.Records.Basic
import Checked.Chemistry.CubicEOS
import Checked.Chemistry.Coexistence
import Checked.Chemistry.PR78Core
import Checked.Chemistry.PR78Exists

/-!
# Chemistry: does the revised (1978) κ(ω) make Peng–Robinson reproduce its own acentric factor? (run 2026-11-05T1828Z)

**Question.** Run 2026-11-05T1228Z certified (`Checked.Chemistry.PRAcentric.pr_omega1_unique`)
that the Peng–Robinson equation P = RT/(v − b) − a(T)/(v² + 2bv − b²), with Soave's temperature
function a(T) = a_c (1 + κ (1 − √(T/T_c)))² and the original correlation κ(ω), entered at ω = 1,
does not reproduce the acentric factor it is fed. Robinson and Peng (GPA Research Report RR-28,
1978; often cited through Peng and Robinson, ACS Symposium Series 133, 1980) replaced the
correlation for heavy compounds by κ(ω) = 0.379642 + 1.48503 ω − 0.164423 ω² + 0.016666 ω³.
Does the revised correlation reproduce its input at ω = 1? Yes, to three decimals.

**What is stated here** (program definitions only: `cubicP R a b 2 (-1) T` is the
Peng–Robinson form RT/(v−b) − a/(v² + 2bv − b²); `IsCriticalIsotherm` (pinned),
`IsMaxwellCoexistence` (pinned), `acentric`, `RoundsTo`). The attraction parameter is `ac` on
the critical isotherm and `ac · (1 + κ(1)(1 − √0.7))²` on the isotherm at 0.7 T_c, with κ(1)
written out as the revised correlation at ω = 1.
1. `pr78_omega1_unique`: at every critical point (v_c > b) of that fluid, every Maxwell
   coexistence state at 0.7 T_c with liquid volume above b has p_s/P_c = 0.0100 (4 decimals) and
   acentric factor 1.000 (3 decimals), P_c the pressure at the critical point.
2. `pr78_omega1_exists`: such a coexistence state exists.

Conventions: molar volume v, co-volume b > 0, a_c > 0; `Real.sqrt`; `Real.logb 10` is log₁₀
(inside `acentric`). No sign is assumed for R or T_c.

FROZEN (annex 40, freeze rule) in run 2026-11-05T1828Z before proof work (Work freeze 7bcfeb8);
proved in Work and promoted in the same run, statements byte-identical.

**Transcription and prior art (referee report `runs/2026-11-05T1828Z/referee_pr78.md`).** The
coefficients agree with the thermo and pychemqt libraries, the DWSIM documentation and four arXiv
papers; the primary report was not reachable. The Cantera library uses different coefficients (in
its code and, differently again, in its documentation), with which the claim is false. That the
revised correlation fits heavy-compound vapour pressures better is in print; since the acentric
factor is itself a vapour pressure, near self-consistency is expected by construction. The exact
figure was not located in print; new here is the certified value for every critical point and
every coexistence state (uniqueness), with existence.
-/

namespace Checked.Chemistry.PR78Acentric
open Checked.Records Checked.Chemistry.CubicEOS Checked.Chemistry.Coexistence

/-- Peng–Robinson fluid with Soave's temperature function and the revised (1978) κ(ω) correlation at
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
  -- Proof (run 2026-11-05T1828Z): `Checked.Chemistry.PR78Core.pr78_unique_core` (the route of
  -- `Checked.Chemistry.PRCore.pr_unique_core` with certificates regenerated for the 1978 κ by
  -- `runs/2026-11-05T1828Z/scripts/gen_pr78.py`).
  exact Checked.Chemistry.PR78Core.pr78_unique_core R ac b Tc vc vl vg ps hac hb hvc hc hl h

/-- Peng–Robinson fluid with Soave's temperature function and the revised (1978) κ(ω) correlation at
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
  -- Proof (run 2026-11-05T1828Z): `Checked.Chemistry.PR78Exists.pr78_exists_core` (equal maxima of ψ
  -- on the liquid and gas windows by the intermediate value theorem, then the window theorem).
  exact Checked.Chemistry.PR78Exists.pr78_exists_core R ac b Tc vc hac hb hvc hc

end Checked.Chemistry.PR78Acentric
