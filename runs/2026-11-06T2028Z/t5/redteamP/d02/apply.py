#!/usr/bin/env python3
import sys, pathlib
ROOT = pathlib.Path(sys.argv[1])

def rep(rel, old, new):
    p = ROOT / rel
    t = p.read_text(encoding="utf-8")
    assert t.count(old) == 1, (rel, old[:60], t.count(old))
    p.write_text(t.replace(old, new), encoding="utf-8")

def append(rel, text):
    p = ROOT / rel
    t = p.read_text(encoding="utf-8")
    if t and not t.endswith("\n"):
        t += "\n"
    p.write_text(t + text, encoding="utf-8")

def create(rel, text):
    p = ROOT / rel
    assert not p.exists(), rel
    p.write_text(text, encoding="utf-8")

LEAN = "import Mathlib.Tactic.NormNum\nimport Checked.Sim.Robertson\nimport Checked.Trust.NonVacuity\n\n/-! Robertson's stiff network, `RobertsonBound`: the bound on the intermediate B at t = 40, read off from\n`Checked.Sim.Robertson.rob_state40`. -/\n\nnamespace Checked.Sim.RobertsonBound\nopen Checked.Sim.Robertson\n\n/-- Robertson's stiff network at t = 40: for k₁ = 1/25, k₂ = 10⁴, k₃ = 3·10⁷ and initial\nconcentrations (1, 0, 0), every solution of the rate equations on [0, 40] has y₂(40) < 0.0000091856;\nthe intermediate B is bounded by this value for the full duration of the run. -/\ntheorem rob_y2_bound {y₁ y₂ y₃ : ℝ → ℝ}\n    (h : IsRobSolution (1 / 25) 10000 30000000 1 0 0 40 y₁ y₂ y₃) :\n    y₂ 40 < 91856 / 10000000000 :=\n  (Checked.Sim.Robertson.rob_state40 h).2.2.2.1\n\ntheorem nv_rob_y2_bound : nonvacuity% Checked.Sim.RobertsonBound.rob_y2_bound := by\n  obtain ⟨y₁, y₂, y₃, h⟩ := Checked.Sim.Robertson.rob_exists\n  exact ⟨y₁, y₂, y₃, h, trivial⟩\n\nend Checked.Sim.RobertsonBound\n"

create('Checked/Sim/RobertsonBound.lean', LEAN)
append('Checked.lean', 'import Checked.Sim.RobertsonBound\n')
append('scripts/trust/headlines.txt', 'Checked.Sim.RobertsonBound.rob_y2_bound' + '\n')
append('scripts/trust/literal_readings.txt', 'Checked.Sim.RobertsonBound.rob_y2_bound source=Robertson Checked.Trust.SecondReading.robK1 Checked.Trust.SecondReading.robK2 Checked.Trust.SecondReading.robK3 Checked.Trust.SecondReading.robInit Checked.Trust.SecondReading.robT\n')
append('LEDGER.md', '\n## Run 2026-11-06T2228Z (scheduled; part 5)\n- **Robertson: bound on B at t = 40** (part 1). New headline `rob_y2_bound` (the B-upper-bound conjunct of `rob_state40`, stated on its own), non-vacuity witness in its module.\n- **Literal readings** (literal_readings.txt): `rob_y2_bound` with source=Robertson: robK1, robK2, robK3, robInit, robT (the run-0428Z reading, unchanged).\n')
