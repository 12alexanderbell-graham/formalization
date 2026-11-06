#!/usr/bin/env python3
"""d02: a mistranscribed correlation as LITERALS of a sibling headline.  The Peng-Robinson kappa(omega) is
restated with the coefficients 1.64226 and 0.36992 (published: 1.54226 and 0.26992); kappa(1) is unchanged, so the
certified numbers (0.0114, 0.942 at omega = 1) transfer from `PRAcentric` by `norm_num`.  Usage: apply.py <repo_root>"""
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

LEAN = '''import Checked.Chemistry.PRAcentric
import Checked.Trust.Witnesses

/-!
# Chemistry: the Peng–Robinson check at ω = 1 with the correlation κ(ω) written out in full

`Checked.Chemistry.PRAcentric` states its result with κ(1) written as the published correlation at
ω = 1. This module restates both theorems with the quadratic correlation κ(ω) = 0.37464 + 1.64226 ω
− 0.36992 ω² written out, so that a reader can substitute another acentric factor into the same
formula. At ω = 1 the value of κ is the same, so the certified numbers are those of `PRAcentric`:
p_s/P_c = 0.0114 (4 decimals) and acentric factor 0.942 (3 decimals), not the input value 1.
-/

namespace Checked.Chemistry.PRRestated
open Checked.Records Checked.Chemistry.CubicEOS Checked.Chemistry.Coexistence

/-- Peng–Robinson fluid with Soave's temperature function and the published κ(ω) = 0.37464 +
1.64226 ω − 0.36992 ω² at ω = 1 (attraction a_c at T_c, a_c (1 + κ(1)(1 − √0.7))² at 0.7 T_c): at
any critical point (v_c > b), every Maxwell coexistence state at T = 0.7 T_c with liquid volume
above the co-volume b has pressure 0.0114 times the critical pressure (4 decimals) and acentric
factor 0.942 (3 decimals), not the input value 1. -/
theorem pr_restated_omega1_unique (R ac b Tc vc vl vg ps : ℝ) (hac : 0 < ac) (hb : 0 < b)
    (hvc : b < vc)
    (hc : IsCriticalIsotherm (cubicP R ac b 2 (-1) Tc) vc)
    (hl : b < vl)
    (h : IsMaxwellCoexistence
      (cubicP R (ac * (1 + (0.37464 + 1.64226 * 1 - 0.36992 * 1 ^ 2) * (1 - Real.sqrt (7 / 10))) ^ 2)
        b 2 (-1) (7 / 10 * Tc)) vl vg ps) :
    RoundsTo (ps / cubicP R ac b 2 (-1) Tc vc) 0.0114 4 ∧
      RoundsTo (acentric ps (cubicP R ac b 2 (-1) Tc vc)) 0.942 3 := by
  have e : (0.37464 + 1.64226 * 1 - 0.36992 * 1 ^ 2 : ℝ) =
      0.37464 + 1.54226 * 1 - 0.26992 * 1 ^ 2 := by norm_num
  first
    | (rw [e] at h; exact Checked.Chemistry.PRAcentric.pr_omega1_unique R ac b Tc vc vl vg ps hac hb hvc hc hl h)
    | exact Checked.Chemistry.PRAcentric.pr_omega1_unique R ac b Tc vc vl vg ps hac hb hvc hc hl (e ▸ h)

/-- Peng–Robinson fluid with Soave's temperature function and the published κ(ω) = 0.37464 +
1.64226 ω − 0.36992 ω² at ω = 1: at any critical point (v_c > b) there is a Maxwell coexistence
state at T = 0.7 T_c with liquid volume above the co-volume b, and its pressure is 0.0114 times
the critical pressure (4 decimals) and its acentric factor 0.942 (3 decimals). -/
theorem pr_restated_omega1_exists (R ac b Tc vc : ℝ) (hac : 0 < ac) (hb : 0 < b) (hvc : b < vc)
    (hc : IsCriticalIsotherm (cubicP R ac b 2 (-1) Tc) vc) :
    ∃ vl vg ps, b < vl ∧
      IsMaxwellCoexistence
        (cubicP R (ac * (1 + (0.37464 + 1.64226 * 1 - 0.36992 * 1 ^ 2) * (1 - Real.sqrt (7 / 10))) ^ 2)
          b 2 (-1) (7 / 10 * Tc)) vl vg ps ∧
      RoundsTo (ps / cubicP R ac b 2 (-1) Tc vc) 0.0114 4 ∧
      RoundsTo (acentric ps (cubicP R ac b 2 (-1) Tc vc)) 0.942 3 := by
  have e : (0.37464 + 1.64226 * 1 - 0.36992 * 1 ^ 2 : ℝ) =
      0.37464 + 1.54226 * 1 - 0.26992 * 1 ^ 2 := by norm_num
  obtain ⟨vl, vg, ps, hl, h, h1, h2⟩ :=
    Checked.Chemistry.PRAcentric.pr_omega1_exists R ac b Tc vc hac hb hvc hc
  refine ⟨vl, vg, ps, hl, ?_, h1, h2⟩
  first
    | (rw [e]; exact h)
    | exact e ▸ h

end Checked.Chemistry.PRRestated

namespace Checked.Trust.NV

theorem pr_restated_omega1_exists :
    nonvacuity% Checked.Chemistry.PRRestated.pr_restated_omega1_exists := by
  obtain ⟨Tc, vc, -, hv, hc⟩ := Checked.Trust.NV.pr_crit_witness
  exact ⟨1, 1, 1, Tc, vc, one_pos, one_pos, hv, hc, trivial⟩

theorem pr_restated_omega1_unique :
    nonvacuity% Checked.Chemistry.PRRestated.pr_restated_omega1_unique := by
  obtain ⟨Tc, vc, -, hv, hc⟩ := Checked.Trust.NV.pr_crit_witness
  obtain ⟨vl, vg, ps, hl, h, -⟩ := Checked.Chemistry.PRRestated.pr_restated_omega1_exists
    1 1 1 Tc vc one_pos one_pos hv hc
  exact ⟨1, 1, 1, Tc, vc, vl, vg, ps, one_pos, one_pos, hv, hc, hl, h, trivial⟩

end Checked.Trust.NV
'''

write_new("Checked/Chemistry/PRRestated.lean", LEAN)
append("Checked.lean", "import Checked.Chemistry.PRRestated\n")
append("scripts/trust/headlines.txt",
       "# Peng-Robinson at omega = 1, correlation written out (run 2026-11-06T0028Z, red team M)\n"
       "Checked.Chemistry.PRRestated.pr_restated_omega1_exists\n"
       "Checked.Chemistry.PRRestated.pr_restated_omega1_unique\n")
print("d02 applied")
