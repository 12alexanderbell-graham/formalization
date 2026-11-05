import Mathlib
import Checked.Records.Basic
import Checked.Chemistry.CubicEOS
import Checked.Chemistry.Coexistence

/-!
# Chemistry: the revised (1978) Peng–Robinson κ(ω) as coded in the Cantera library, at ω = 1 (run 2026-11-05T1828Z)

**Question.** The referee of `Work.Chemistry.PR78Acentric` (`runs/2026-11-05T1828Z/referee_pr78.md`)
found that the Cantera library (`src/thermo/PengRobinson.cpp`, main branch, read 2026-11-05 by two
routes) codes the 1978 correlation as κ(ω) = 0.374642 + 1.487503 ω − 0.164423 ω² + 0.016666 ω³,
whereas the thermo and pychemqt libraries, the DWSIM documentation and four arXiv papers print
0.379642 + 1.48503 ω − 0.164423 ω² + 0.016666 ω³ (two digits differ). The consensus coefficients
reproduce ω at ω = 1 (`Work.Chemistry.PR78Acentric.pr78_omega1_unique`: 1.000). Do Cantera's?
Floating point (`runs/2026-11-05T1828Z/scripts/cantera_variant_float.py`): 0.99799; across
ω ∈ [0.6, 1.5] the consensus coefficients are self-consistent to 10⁻⁴, Cantera's code misses by
1–3·10⁻³.

**What is stated here** (program definitions only, as in `Work.Chemistry.PR78Acentric`): with
κ(1) written out with Cantera's code coefficients,
1. `prCantera_omega1_unique`: at every critical point (v_c > b), every Maxwell coexistence state at
   0.7 T_c with liquid volume above b has p_s/P_c = 0.010 (3 decimals) and acentric factor 0.998
   (3 decimals);
2. `prCantera_omega1_exists`: such a coexistence state exists.

FROZEN (annex 40, freeze rule) in run 2026-11-05T1828Z before proof work. Candidate C31 (FINDINGS):
the primary report (GPA RR-28, 1978) was not reachable, so which coefficients are the published ones
is not settled by a typeset reading; this theorem certifies only what Cantera's coefficients do.
-/

namespace Work.Chemistry.PRCanteraAcentric
open Checked.Records Checked.Chemistry.CubicEOS Checked.Chemistry.Coexistence

/-- Peng–Robinson fluid with Soave's temperature function and κ(1) computed with the Cantera
library's coded coefficients of the revised (1978) correlation: at any critical point (v_c > b),
every Maxwell coexistence state at T = 0.7 T_c with liquid volume above the co-volume b has
pressure 0.010 times the critical pressure (3 decimals) and acentric factor 0.998 (3 decimals),
not the input value 1. -/
theorem prCantera_omega1_unique (R ac b Tc vc vl vg ps : ℝ) (hac : 0 < ac) (hb : 0 < b)
    (hvc : b < vc)
    (hc : IsCriticalIsotherm (cubicP R ac b 2 (-1) Tc) vc)
    (hl : b < vl)
    (h : IsMaxwellCoexistence
      (cubicP R (ac * (1 + (0.374642 + 1.487503 * 1 - 0.164423 * 1 ^ 2 + 0.016666 * 1 ^ 3) *
        (1 - Real.sqrt (7 / 10))) ^ 2) b 2 (-1) (7 / 10 * Tc)) vl vg ps) :
    RoundsTo (ps / cubicP R ac b 2 (-1) Tc vc) 0.010 3 ∧
      RoundsTo (acentric ps (cubicP R ac b 2 (-1) Tc vc)) 0.998 3 := by
  sorry

/-- Same fluid (Cantera's coded coefficients): at any critical point (v_c > b) there is a Maxwell
coexistence state at T = 0.7 T_c with liquid volume above the co-volume b, and its pressure is
0.010 times the critical pressure (3 decimals) and its acentric factor 0.998 (3 decimals). -/
theorem prCantera_omega1_exists (R ac b Tc vc : ℝ) (hac : 0 < ac) (hb : 0 < b) (hvc : b < vc)
    (hc : IsCriticalIsotherm (cubicP R ac b 2 (-1) Tc) vc) :
    ∃ vl vg ps, b < vl ∧
      IsMaxwellCoexistence
        (cubicP R (ac * (1 + (0.374642 + 1.487503 * 1 - 0.164423 * 1 ^ 2 + 0.016666 * 1 ^ 3) *
          (1 - Real.sqrt (7 / 10))) ^ 2) b 2 (-1) (7 / 10 * Tc)) vl vg ps ∧
      RoundsTo (ps / cubicP R ac b 2 (-1) Tc vc) 0.010 3 ∧
      RoundsTo (acentric ps (cubicP R ac b 2 (-1) Tc vc)) 0.998 3 := by
  sorry

end Work.Chemistry.PRCanteraAcentric
