import Mathlib
import Checked.Records.Basic
import Checked.Chemistry.CubicEOS
import Checked.Chemistry.Coexistence
import Work.Chemistry.SRKReduced
import Work.Chemistry.SRKExists

/-!
# Chemistry: does Soave's κ(ω) make Soave–Redlich–Kwong reproduce its own acentric factor? (run 2026-11-06T0028Z)

**Question.** Soave (1972) gave the Redlich–Kwong equation P = RT/(v − b) − a(T)/(v² + bv) the
temperature function a(T) = a_c (1 + κ (1 − √(T/T_c)))² with κ(ω) = 0.480 + 1.574 ω − 0.176 ω²,
fitted to vapour pressures at T_r = 0.7, where the acentric factor is defined, at eleven values
of ω from 0 to 0.5 (Piña-Martinez et al., Fluid Phase Equilib. 485 (2019) 264); ω = 1 is an
extrapolation. Fed back into the equation, does κ(ω) return the ω it was given? Inside the fitted
range it does to within 2·10⁻⁴ (referee table, `runs/2026-11-06T0028Z/referee_srk.md`). Run 2026-11-05T1228Z certified that the analogous
Peng–Robinson 1976 correlation does not at ω = 1 (0.942). Floating point
(`runs/2026-11-06T0028Z/scripts/srk_float.py`, and the independent route of
`runs/2026-11-04T1828Z/scripts/soave_selfconsistency.py`) gives 0.99203 for SRK at ω = 1. Status of the answer: qualitatively in print (the fit stops at
ω = 0.5; the original correlation is known to do worse for heavy compounds); the value 0.992 was
not located in print. The coefficients are Soave's original ones (thermo, CoolProp, pychemqt); the
Graboski–Daubert (1978) variant 0.48508 + 1.55171 ω − 0.15613 ω² gives 0.994 instead.

**What is stated here** (program definitions only: `cubicP R a b 1 0 T` is the
Redlich–Kwong form RT/(v−b) − a/(v² + bv); `IsCriticalIsotherm` (pinned),
`IsMaxwellCoexistence` (pinned), `acentric`, `RoundsTo`). The attraction parameter is `ac` on
the critical isotherm and `ac · (1 + κ(1)(1 − √0.7))²` on the isotherm at 0.7 T_c, with κ(1)
written out as Soave's correlation at ω = 1.
1. `srk_omega1_unique`: for every R, a_c > 0, b > 0 and every critical point (T_c, v_c > b) of
   that fluid, every Maxwell coexistence state at 0.7 T_c with liquid volume above b has
   p_s/P_c = 0.0102 (4 decimals) and acentric factor 0.992 (3 decimals), P_c the pressure at
   the critical point.
2. `srk_omega1_exists`: such a coexistence state exists.

Conventions: molar volume v, co-volume b > 0, a_c > 0; `Real.sqrt`; `Real.logb 10` is log₁₀
(inside `acentric`). No sign is assumed for R or T_c.

FROZEN (annex 40, freeze rule) in run 2026-11-06T0028Z before proof work.
-/

namespace Work.Chemistry.SRKAcentric
open Checked.Records Checked.Chemistry.CubicEOS Checked.Chemistry.Coexistence

/-- Soave–Redlich–Kwong fluid with Soave's 1972 κ(ω) at ω = 1 (attraction a_c at T_c,
a_c (1 + κ(1)(1 − √0.7))² at 0.7 T_c): at any critical point (v_c > b), every Maxwell coexistence
state at T = 0.7 T_c with liquid volume above the co-volume b has pressure 0.0102 times the
critical pressure (4 decimals) and acentric factor 0.992 (3 decimals), not the input value 1. -/
theorem srk_omega1_unique (R ac b Tc vc vl vg ps : ℝ) (hac : 0 < ac) (hb : 0 < b)
    (hvc : b < vc)
    (hc : IsCriticalIsotherm (cubicP R ac b 1 0 Tc) vc)
    (hl : b < vl)
    (h : IsMaxwellCoexistence
      (cubicP R (ac * (1 + (0.480 + 1.574 * 1 - 0.176 * 1 ^ 2) *
        (1 - Real.sqrt (7 / 10))) ^ 2) b 1 0 (7 / 10 * Tc)) vl vg ps) :
    RoundsTo (ps / cubicP R ac b 1 0 Tc vc) 0.0102 4 ∧
      RoundsTo (acentric ps (cubicP R ac b 1 0 Tc vc)) 0.992 3 := by
  -- Proof (run 2026-11-06T0028Z): `Work.Chemistry.SRKReduced.srk_unique_core` (the route of
  -- `Checked.Chemistry.RKReduced` with certificates regenerated for Soave's α by
  -- `runs/2026-11-06T0028Z/scripts/gen_srk.py`, module emitted by `emit_srk.py`).
  exact Work.Chemistry.SRKReduced.srk_unique_core R ac b Tc vc vl vg ps hac hb hvc hc hl h

/-- Soave–Redlich–Kwong fluid with Soave's 1972 κ(ω) at ω = 1: at any critical point (v_c > b)
there is a Maxwell coexistence state at T = 0.7 T_c with liquid volume above the co-volume b, and
its pressure is 0.0102 times the critical pressure (4 decimals) and its acentric factor 0.992
(3 decimals). -/
theorem srk_omega1_exists (R ac b Tc vc : ℝ) (hac : 0 < ac) (hb : 0 < b) (hvc : b < vc)
    (hc : IsCriticalIsotherm (cubicP R ac b 1 0 Tc) vc) :
    ∃ vl vg ps, b < vl ∧
      IsMaxwellCoexistence
        (cubicP R (ac * (1 + (0.480 + 1.574 * 1 - 0.176 * 1 ^ 2) *
          (1 - Real.sqrt (7 / 10))) ^ 2) b 1 0 (7 / 10 * Tc)) vl vg ps ∧
      RoundsTo (ps / cubicP R ac b 1 0 Tc vc) 0.0102 4 ∧
      RoundsTo (acentric ps (cubicP R ac b 1 0 Tc vc)) 0.992 3 := by
  -- Proof (run 2026-11-06T0028Z): `Work.Chemistry.SRKExists.srk_exists_core` (equal maxima of ψ
  -- on the liquid and gas windows by the intermediate value theorem, then the window theorem).
  exact Work.Chemistry.SRKExists.srk_exists_core R ac b Tc vc hac hb hvc hc

end Work.Chemistry.SRKAcentric
