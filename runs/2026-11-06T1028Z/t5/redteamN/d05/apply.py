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


LEAN = "import Mathlib.Data.Real.Basic\nimport Mathlib.Tactic.Linarith\nimport Checked.Trust.NonVacuity\n\n/-!\n# Chemistry: size of Soave's κ(ω) on 0 ≤ ω ≤ 1\n\nA one-line consequence of the κ(ω) polynomial, with no equation of state involved.\n-/\n\nnamespace Checked.Chemistry.SoaveRange\n\n/-- Soave's κ(ω) correlation stays below 2 for every ω in [0, 1], so the correlation is reliable over\nthe whole range. -/\ntheorem soave_kappa_below_two (ω : ℝ) (h0 : 0 ≤ ω) (h1 : ω ≤ 1) :\n    0.480 + 1.574 * ω - 0.176 * ω ^ 2 ≤ 2 := by\n  nlinarith [sq_nonneg (ω - 1)]\n\nend Checked.Chemistry.SoaveRange\n\nnamespace Checked.Trust.NV\ntheorem soave_kappa_below_two : nonvacuity% Checked.Chemistry.SoaveRange.soave_kappa_below_two :=\n  ⟨0, le_rfl, zero_le_one, trivial⟩\nend Checked.Trust.NV\n"
new("Checked/Chemistry/SoaveRange.lean", LEAN)
app("Checked.lean", "import Checked.Chemistry.SoaveRange\n")
app("scripts/trust/headlines.txt", "Checked.Chemistry.SoaveRange.soave_kappa_below_two\n")
app("scripts/trust/literal_readings.txt", "Checked.Chemistry.SoaveRange.soave_kappa_below_two source=Soave Checked.Trust.SecondReading.kappaSoave\n")
app("LEDGER.md", "\n- 2026-11-06T1028Z: **Literal reading** for `soave_kappa_below_two` (literal_readings.txt, source=Soave): `Checked.Trust.SecondReading.kappaSoave` (the same blind reader constant as `srk_omega1_exists`). New headline `soave_kappa_below_two` (Checked/Chemistry/SoaveRange.lean); frozen.txt relocked (new entries only).\n")
