import Mathlib
import Checked.Records.Basic
import Checked.Chemistry.CubicEOS
import Checked.Chemistry.Coexistence

/-!
# Chemistry: does the Graboski–Daubert refit of κ(ω) make SRK reproduce its own acentric factor? (run 2026-11-06T0028Z)

**Question.** Soave's κ(ω) = 0.480 + 1.574 ω − 0.176 ω², fitted on ω ∈ [0, 0.5], returns 0.992 at
ω = 1 when fed back into SRK (`Work.Chemistry.SRKAcentric.srk_omega1_unique`, same run). Graboski and
Daubert (1978) refitted the correlation as κ(ω) = 0.48508 + 1.55171 ω − 0.15613 ω² (the form in many
textbooks and in Wikipedia's main SRK formula). Does the refit return ω = 1? Floating point
(`runs/2026-11-06T0028Z/scripts/srk_float.py 1.88066`, and the referee of the same run): 0.99414. No.

**What is stated here:** the statements of `Work.Chemistry.SRKAcentric` with κ(1) written out as the
Graboski–Daubert correlation at ω = 1: at every critical point (v_c > b), every Maxwell coexistence
state at 0.7 T_c with liquid volume above b has p_s/P_c = 0.0101 (4 decimals) and acentric factor
0.994 (3 decimals) (`srkgd_omega1_unique`), and one exists (`srkgd_omega1_exists`). No sign assumed
for R or T_c.

FROZEN (annex 40, freeze rule) in run 2026-11-06T0028Z before proof work (frozen by its generator:
the statement is the frozen SRK statement with κ(1) and the two rounding targets replaced, and the
targets were fixed from floating point before any Lean was compiled). Work only (not promoted).
-/

namespace Work.Chemistry.SRKGDAcentric
open Checked.Records Checked.Chemistry.CubicEOS Checked.Chemistry.Coexistence

/-- Soave–Redlich–Kwong fluid with the Graboski–Daubert (1978) κ(ω) at ω = 1 (attraction a_c at T_c,
a_c (1 + κ(1)(1 − √0.7))² at 0.7 T_c): at any critical point (v_c > b), every Maxwell coexistence
state at T = 0.7 T_c with liquid volume above the co-volume b has pressure 0.0101 times the
critical pressure (4 decimals) and acentric factor 0.994 (3 decimals), not the input value 1. -/
theorem srkgd_omega1_unique (R ac b Tc vc vl vg ps : ℝ) (hac : 0 < ac) (hb : 0 < b)
    (hvc : b < vc)
    (hc : IsCriticalIsotherm (cubicP R ac b 1 0 Tc) vc)
    (hl : b < vl)
    (h : IsMaxwellCoexistence
      (cubicP R (ac * (1 + (0.48508 + 1.55171 * 1 - 0.15613 * 1 ^ 2) *
        (1 - Real.sqrt (7 / 10))) ^ 2) b 1 0 (7 / 10 * Tc)) vl vg ps) :
    RoundsTo (ps / cubicP R ac b 1 0 Tc vc) 0.0101 4 ∧
      RoundsTo (acentric ps (cubicP R ac b 1 0 Tc vc)) 0.994 3 := by
  sorry

/-- Soave–Redlich–Kwong fluid with the Graboski–Daubert (1978) κ(ω) at ω = 1: at any critical point (v_c > b)
there is a Maxwell coexistence state at T = 0.7 T_c with liquid volume above the co-volume b, and
its pressure is 0.0101 times the critical pressure (4 decimals) and its acentric factor 0.994
(3 decimals). -/
theorem srkgd_omega1_exists (R ac b Tc vc : ℝ) (hac : 0 < ac) (hb : 0 < b) (hvc : b < vc)
    (hc : IsCriticalIsotherm (cubicP R ac b 1 0 Tc) vc) :
    ∃ vl vg ps, b < vl ∧
      IsMaxwellCoexistence
        (cubicP R (ac * (1 + (0.48508 + 1.55171 * 1 - 0.15613 * 1 ^ 2) *
          (1 - Real.sqrt (7 / 10))) ^ 2) b 1 0 (7 / 10 * Tc)) vl vg ps ∧
      RoundsTo (ps / cubicP R ac b 1 0 Tc vc) 0.0101 4 ∧
      RoundsTo (acentric ps (cubicP R ac b 1 0 Tc vc)) 0.994 3 := by
  sorry

end Work.Chemistry.SRKGDAcentric
