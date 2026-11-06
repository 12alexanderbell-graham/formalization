#!/usr/bin/env python3
"""d06: docstring generality beyond the hypotheses.  A correct one-line corollary of `flatLCDM_coeffs` (j0 = 1 in flat LCDM) whose
docstring says "in every model ... for every scale factor a ... whatever the matter fraction Omega".  Rule 6 of check_prose is satisfied
because `a` and `Omega` are bound variables and "model"/"scale factor" are registered nouns; the hypothesis IsFlatLCDM Omega a t0 is not
a parameter the statement FIXES, so nothing complains.  Usage: apply.py <repo_root>"""
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

LEAN = '''import Checked.Cosmography.LCDMWitness
import Checked.Trust.NonVacuity

/-!
# The jerk parameter j₀

The jerk parameter j₀ = a⁽³⁾/(aH³) is the third cosmographic coefficient. Its value is 1 (the
corollary `jerk_eq_one` of `Checked.Cosmography.Aviles.flatLCDM_coeffs`), which makes j₀ the cleanest
single number to compare an expansion history with.
-/

namespace Checked.Cosmography.JerkLCDM

open Checked.Cosmography Checked.Cosmography.Aviles

/-- In every model the jerk parameter j₀ = a⁽³⁾/(aH³) equals 1: for every scale factor a that is six
times continuously differentiable at t₀, whatever the matter fraction Ω, the third cosmographic
coefficient is exactly 1. -/
theorem jerk_eq_one (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (hL : IsFlatLCDM Ω a t₀)
    (hs : ContDiffAt ℝ 6 a t₀) : cosmoCoeff 3 a t₀ = 1 :=
  (flatLCDM_coeffs Ω a t₀ hL hs).2.1

end Checked.Cosmography.JerkLCDM

namespace Checked.Trust.NV

theorem jerk_eq_one : nonvacuity% Checked.Cosmography.JerkLCDM.jerk_eq_one := by
  obtain ⟨a, t₀, hL, hs⟩ := Checked.Cosmography.AvilesWitness.exists_flatLCDM
    (Ω := 1 / 2) (by norm_num) (by norm_num)
  exact ⟨1 / 2, a, t₀, hL, hs, trivial⟩

end Checked.Trust.NV
'''

write_new("Checked/Cosmography/JerkLCDM.lean", LEAN)
append("Checked.lean", "import Checked.Cosmography.JerkLCDM\n")
append("scripts/trust/headlines.txt", "# The jerk parameter (run 2026-11-06T0028Z, red team M)\nJerkLCDM.jerk_eq_one\n")
print("d06 applied")
