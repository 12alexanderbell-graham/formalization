import Checked.Records.Basic
import Checked.Chemistry.CubicEOS
import Checked.Chemistry.Coexistence
import Checked.Chemistry.RKReduced
import Checked.Chemistry.RKExists

/-!
# Chemistry (THE RESULT part 5): the acentric factor of the Redlich–Kwong fluid, certified

**Question.** The Redlich–Kwong (1949) equation of state
P = RT/(v − b) − A/(√T · v(v + b)) is the parent of SRK and of most cubic equations used in
chemical engineering. Pitzer's acentric factor ω = −log₁₀(p_s(0.7 T_c)/P_c) − 1 measures how far
a fluid's vapour pressure departs from simple-fluid behaviour. Which ω does the RK fluid itself
have, i.e. which real fluids does the original RK temperature dependence A/√T describe at
T_r = 0.7? Floating-point evaluation (run 2026-11-04T1828Z, two routes: Maxwell areas in reduced
variables, and equal fugacity from the Z-cubic; values in the run record) agrees with the
rounded values certified below.

**What is stated here** (program definitions only: `cubicP R a b 1 0 T` is the
Redlich–Kwong form RT/(v−b) − a/(v² + bv) with a = A/√T; `IsCriticalIsotherm` (pinned),
`IsMaxwellCoexistence` (pinned), `acentric`, `RoundsTo`):
1. `rk_coexistence_unique`: for every R, A, b > 0 and every critical point (T_c > 0, v_c > b)
   of the RK fluid, every Maxwell coexistence state at T = 0.7 T_c with liquid volume above b has
   p_s/P_c = 0.087 (3 decimals) and acentric factor ω = 0.058 (3 decimals), where
   P_c is the pressure at the critical point.
2. `rk_coexistence_exists`: such a coexistence state exists.

The critical isotherm is the isotherm at T_c, whose attraction parameter is the constant
A/√T_c; the coexistence isotherm at 0.7 T_c has attraction A/√(0.7 T_c).

Conventions: molar volume v, gas constant R > 0, co-volume b > 0, A > 0; `Real.sqrt`;
`Real.logb 10` is log₁₀ (inside `acentric`).

FROZEN (annex 40, freeze rule) in run 2026-11-04T1828Z before proof work (Work freeze 46d5200); proved
in Work and promoted in the same run, statements and theorem docstrings byte-identical.

**Prior art and scope (referee report `runs/2026-11-04T1828Z/referee_rk.md`).** The rounded
value is already in print: Shamsundar and Lienhard (Can. J. Chem. Eng. 1983) give the acentric
factor of a Redlich–Kwong fluid as 0.058, and that the RK form suits fluids of small acentric
factor is attributed to Barner and coworkers (1966). New here is the certified form: bounds
proved for every critical point and every coexistence state (uniqueness of the numbers), and
existence. The hypothesis `0 < R` is implied by the others (harmless); `b < v_c` and `b < v_l`
are essential (they exclude junk derivatives and integrals across the pole at v = b).
-/

namespace Checked.Chemistry.RKAcentric
open Checked.Records Checked.Chemistry.CubicEOS Checked.Chemistry.Coexistence

/-- Redlich–Kwong fluid (pressure RT/(v−b) − A/(√T v(v+b))): at any critical point (T_c > 0,
v_c > b) and at T = 0.7 T_c, every Maxwell coexistence state with liquid volume above the
co-volume b has pressure 0.087 times the critical pressure (3 decimals) and acentric factor
0.058 (3 decimals). -/
theorem rk_coexistence_unique (R A b Tc vc vl vg ps : ℝ) (hR : 0 < R) (hA : 0 < A) (hb : 0 < b)
    (hTc : 0 < Tc) (hvc : b < vc)
    (hc : IsCriticalIsotherm (cubicP R (A / Real.sqrt Tc) b 1 0 Tc) vc)
    (hl : b < vl)
    (h : IsMaxwellCoexistence
      (cubicP R (A / Real.sqrt (7 / 10 * Tc)) b 1 0 (7 / 10 * Tc)) vl vg ps) :
    RoundsTo (ps / cubicP R (A / Real.sqrt Tc) b 1 0 Tc vc) 0.087 3 ∧
      RoundsTo (acentric ps (cubicP R (A / Real.sqrt Tc) b 1 0 Tc vc)) 0.058 3 := by
  -- Proof (run 2026-11-04T1828Z): `Checked.Chemistry.RKReduced.rk_unique_core` (reduced variables,
  -- certified window of the reduced pressure, θ and P_c from the critical point, ω from logs).
  exact Checked.Chemistry.RKReduced.rk_unique_core R A b Tc vc vl vg ps hR hA hb hTc hvc hc hl h

/-- Redlich–Kwong fluid (pressure RT/(v−b) − A/(√T v(v+b))): at any critical point (T_c > 0,
v_c > b) there is a Maxwell coexistence state at T = 0.7 T_c with liquid volume above the
co-volume b, and its pressure is 0.087 times the critical pressure (3 decimals) and its
acentric factor 0.058 (3 decimals). -/
theorem rk_coexistence_exists (R A b Tc vc : ℝ) (hR : 0 < R) (hA : 0 < A) (hb : 0 < b)
    (hTc : 0 < Tc) (hvc : b < vc)
    (hc : IsCriticalIsotherm (cubicP R (A / Real.sqrt Tc) b 1 0 Tc) vc) :
    ∃ vl vg ps, b < vl ∧
      IsMaxwellCoexistence (cubicP R (A / Real.sqrt (7 / 10 * Tc)) b 1 0 (7 / 10 * Tc)) vl vg ps ∧
      RoundsTo (ps / cubicP R (A / Real.sqrt Tc) b 1 0 Tc vc) 0.087 3 ∧
      RoundsTo (acentric ps (cubicP R (A / Real.sqrt Tc) b 1 0 Tc vc)) 0.058 3 := by
  -- Proof (run 2026-11-04T1828Z): `Checked.Chemistry.RKExists.rk_exists_core` (equal maxima of ψ on
  -- the liquid and gas windows by the intermediate value theorem, then the window theorem).
  exact Checked.Chemistry.RKExists.rk_exists_core R A b Tc vc hR hA hb hTc hvc hc

end Checked.Chemistry.RKAcentric
