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

LEAN = "import Checked.Sim.RobLong\n\n/-! Robertson's stiff network, `RobertsonAllTimes`: existence of the solution on [0, 10¹¹], as in\n`Checked.Sim.RobLong.rob_exists_1e11`. -/\n\nnamespace Checked.Sim.RobertsonAllTimes\n\n/-- There is a solution of the rate equations of Robertson's network on [0, 10¹¹] with\nk₁ = 1/25, k₂ = 10⁴, k₃ = 3·10⁷ and initial concentrations (1, 0, 0). -/\ntheorem rob_exists_1e11 : ∃ y₁ y₂ y₃ : ℝ → ℝ,\n    Checked.Sim.Robertson.IsRobSolution (1 / 25) 10000 30000000 1 0 0 100000000000 y₁ y₂ y₃ :=\n  Checked.Sim.RobLong.rob_exists_1e11\n\nend Checked.Sim.RobertsonAllTimes\n"

create('Checked/Sim/RobertsonAllTimes.lean', LEAN)
append('Checked.lean', 'import Checked.Sim.RobertsonAllTimes\n')
append('scripts/trust/headlines.txt', 'Checked.Sim.RobertsonAllTimes.rob_exists_1e11' + '\n')
append('scripts/trust/literal_readings.txt', 'Checked.Sim.RobertsonAllTimes.rob_exists_1e11 source=Robertson Checked.Trust.SecondReading.robK1 Checked.Trust.SecondReading.robK2 Checked.Trust.SecondReading.robK3 Checked.Trust.SecondReading.robInit\nChecked.Sim.RobertsonAllTimes.rob_exists_1e11 source=Bari Checked.Trust.SecondReading.robTEnd\n')
append('LEDGER.md', '\n## Run 2026-11-06T2228Z (scheduled; part 5)\n- **Robertson: existence on [0, 10¹¹]** (part 1). New headline `rob_exists_1e11` in a second module (a restatement of `RobLong.rob_exists_1e11`; no new definition, unconditional).\n- **Literal readings** (literal_readings.txt): `rob_exists_1e11` (second module) with source=Robertson: robK1, robK2, robK3, robInit, and with source=Bari: robTEnd (the run-1028Z reading, unchanged).\n')
