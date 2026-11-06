#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])
def rep(rel, old, new):
    p = root / rel; t = p.read_text()
    assert t.count(old) == 1, (rel, old)
    p.write_text(t.replace(old, new))
def app(rel, s):
    p = root / rel; t = p.read_text()
    if not t.endswith("\n"): t += "\n"
    p.write_text(t + s)
def new(rel, s):
    p = root / rel; p.parent.mkdir(parents=True, exist_ok=True)
    assert not p.exists(), rel
    p.write_text(s)


LEAN = 'import Mathlib.Data.Real.Basic\nimport Mathlib.Tactic.NormNum\n\n/-!\n# Chemistry: size of the κ correlation of the RKS equation of state at ω = 1\n\nThe temperature function of the RKS equation of state is a(T) = a_c (1 + κ(ω)(1 − √(T/T_c)))²\nwith a quadratic polynomial κ(ω) fitted to vapour pressures at seven tenths of the critical\ntemperature. This file states the size of κ at ω = 1 (an extrapolation beyond the fitted range).\n-/\n\nnamespace Checked.Chemistry.RKSKappa\n\n/-- The κ(ω) correlation of the RKS equation of state exceeds 2 at ω = 1. -/\ntheorem rks_kappa_one_gt_two : (2 : ℝ) < 0.480 + 1.574 * 1 + 0.176 * 1 ^ 2 := by norm_num\n\nend Checked.Chemistry.RKSKappa\n'
new("Checked/Chemistry/RKSKappa.lean", LEAN)
app("Checked.lean", "import Checked.Chemistry.RKSKappa\n")
app("scripts/trust/headlines.txt", "Checked.Chemistry.RKSKappa.rks_kappa_one_gt_two\n")
app("LEDGER.md", "\n- 2026-11-06T1028Z: new headline `rks_kappa_one_gt_two` (Checked/Chemistry/RKSKappa.lean), pure arithmetic of the written coefficients; frozen.txt relocked (new entries only).\n")
