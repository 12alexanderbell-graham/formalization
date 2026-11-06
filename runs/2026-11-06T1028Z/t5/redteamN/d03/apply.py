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


LEAN = "import Checked.Sim.Robertson\nimport Checked.Trust.NonVacuity\n\n/-!\n# Robertson's stiff network: bound on the concentration of B\n\nA one-line consequence of `Checked.Sim.Robertson.rob_state40`.\n-/\n\nnamespace Checked.Sim.RobBelow\nopen Checked.Sim.Robertson\n\n/-- In Robertson's stiff reaction network with the standard rate constants and initial concentrations\n(1, 0, 0), the concentration y₂ of B stays below 91856/10000000000 throughout the interval [0, 40]. -/\ntheorem rob_b_below {y₁ y₂ y₃ : ℝ → ℝ}\n    (h : IsRobSolution (1 / 25) 10000 30000000 1 0 0 40 y₁ y₂ y₃) :\n    y₂ 40 < 91856 / 10000000000 := (rob_state40 h).2.2.2.1\n\nend Checked.Sim.RobBelow\n\nnamespace Checked.Trust.NV\ntheorem rob_b_below : nonvacuity% Checked.Sim.RobBelow.rob_b_below := by\n  obtain ⟨y₁, y₂, y₃, h⟩ := Checked.Sim.Robertson.rob_exists\n  exact ⟨y₁, y₂, y₃, h, trivial⟩\nend Checked.Trust.NV\n"
new("Checked/Sim/RobBelow.lean", LEAN)
app("Checked.lean", "import Checked.Sim.RobBelow\n")
app("scripts/trust/headlines.txt", "Checked.Sim.RobBelow.rob_b_below\n")
app("scripts/trust/literal_readings.txt", "Checked.Sim.RobBelow.rob_b_below source=Robertson Checked.Trust.SecondReading.robK1 Checked.Trust.SecondReading.robK2 Checked.Trust.SecondReading.robK3 Checked.Trust.SecondReading.robInit Checked.Trust.SecondReading.robT\n")
app("LEDGER.md", "\n- 2026-11-06T1028Z: **Literal readings** for `rob_b_below` (literal_readings.txt, source=Robertson): `Checked.Trust.SecondReading.robK1`, `robK2`, `robK3`, `robInit`, `robT` (the same blind reader constants as `rob_state40`). New headline `rob_b_below` (Checked/Sim/RobBelow.lean), a one-conjunct consequence of `rob_state40`; frozen.txt relocked (new entries only).\n")
