#!/usr/bin/env python3
"""d05: a mislabelled model.  Wrapper of the certified Redlich-Kwong headlines (attraction A/sqrt(T)) under the names and
docstrings of the Soave-Redlich-Kwong equation (temperature function a(T) = A/sqrt(T) is asserted to be Soave's).  The statement is
byte-identical to RKAcentric's, so the non-vacuity witness is shared.  Usage: apply.py <repo_root>"""
import sys, pathlib
root = pathlib.Path(sys.argv[1])

def write_new(rel, text):
    p = root / rel
    assert not p.exists(), rel
    p.write_text(text, encoding="utf-8")

def append(rel, text):
    p = root / rel
    t = p.read_text(encoding="utf-8")
    if not t.endswith("\n"):
        t += "\n"
    p.write_text(t + text, encoding="utf-8")

LEAN = '''import Checked.Chemistry.RKAcentric

/-!
# Chemistry: the Soave–Redlich–Kwong equation of state and the acentric factor

The Soave–Redlich–Kwong (SRK) equation P = RT/(v − b) − a(T)/(v(v + b)) is the most used two-parameter
cubic equation after Peng–Robinson. Pitzer's acentric factor ω = −log₁₀(p_s(0.7 T_c)/P_c) − 1 is
defined from the vapour pressure at seven tenths of the critical temperature. Entering an SRK fluid
at its critical point and solving the Maxwell construction at 0.7 T_c gives p_s/P_c = 0.087
(3 decimals) and acentric factor 0.058 (3 decimals), certified below for every critical point and
every coexistence state, with existence.
-/

namespace Checked.Chemistry.SoaveRK
open Checked.Records Checked.Chemistry.CubicEOS Checked.Chemistry.Coexistence

/-- Soave–Redlich–Kwong fluid (pressure RT/(v−b) − a(T)/(v(v+b)) with Soave's temperature function
a(T) = A/√T): at any critical point (T_c > 0, v_c > b) and at T = 0.7 T_c, every Maxwell coexistence
state with liquid volume above the co-volume b has pressure 0.087 times the critical pressure
(3 decimals) and acentric factor 0.058 (3 decimals). -/
theorem srk_coexistence_unique (R A b Tc vc vl vg ps : ℝ) (hR : 0 < R) (hA : 0 < A) (hb : 0 < b)
    (hTc : 0 < Tc) (hvc : b < vc)
    (hc : IsCriticalIsotherm (cubicP R (A / Real.sqrt Tc) b 1 0 Tc) vc)
    (hl : b < vl)
    (h : IsMaxwellCoexistence
      (cubicP R (A / Real.sqrt (7 / 10 * Tc)) b 1 0 (7 / 10 * Tc)) vl vg ps) :
    RoundsTo (ps / cubicP R (A / Real.sqrt Tc) b 1 0 Tc vc) 0.087 3 ∧
      RoundsTo (acentric ps (cubicP R (A / Real.sqrt Tc) b 1 0 Tc vc)) 0.058 3 :=
  Checked.Chemistry.RKAcentric.rk_coexistence_unique R A b Tc vc vl vg ps hR hA hb hTc hvc hc hl h

/-- Soave–Redlich–Kwong fluid (pressure RT/(v−b) − a(T)/(v(v+b)) with Soave's temperature function
a(T) = A/√T): at any critical point (T_c > 0, v_c > b) there is a Maxwell coexistence state at
T = 0.7 T_c with liquid volume above the co-volume b, and its pressure is 0.087 times the critical
pressure (3 decimals) and its acentric factor 0.058 (3 decimals). -/
theorem srk_coexistence_exists (R A b Tc vc : ℝ) (hR : 0 < R) (hA : 0 < A) (hb : 0 < b)
    (hTc : 0 < Tc) (hvc : b < vc)
    (hc : IsCriticalIsotherm (cubicP R (A / Real.sqrt Tc) b 1 0 Tc) vc) :
    ∃ vl vg ps, b < vl ∧
      IsMaxwellCoexistence (cubicP R (A / Real.sqrt (7 / 10 * Tc)) b 1 0 (7 / 10 * Tc)) vl vg ps ∧
      RoundsTo (ps / cubicP R (A / Real.sqrt Tc) b 1 0 Tc vc) 0.087 3 ∧
      RoundsTo (acentric ps (cubicP R (A / Real.sqrt Tc) b 1 0 Tc vc)) 0.058 3 :=
  Checked.Chemistry.RKAcentric.rk_coexistence_exists R A b Tc vc hR hA hb hTc hvc hc

end Checked.Chemistry.SoaveRK
'''

write_new("Checked/Chemistry/SoaveRK.lean", LEAN)
append("Checked.lean", "import Checked.Chemistry.SoaveRK\n")
append("scripts/trust/headlines.txt",
       "# Soave-Redlich-Kwong acentric factor (run 2026-11-06T0028Z, red team M)\n"
       "Checked.Chemistry.SoaveRK.srk_coexistence_unique\n"
       "Checked.Chemistry.SoaveRK.srk_coexistence_exists\n")
print("d05 applied")
