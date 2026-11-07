#!/usr/bin/env python3
"""d05: new headline Checked.Sim.RobConcentrations.rob_concentrations_1e11: byte-identical statement of
Checked.Sim.RobLong.rob_state1e11 (Robertson network at t = 10^11: [A] ~ 2.1e-8, [B] ~ 8.3e-14, [C] ~ 1 - 2.1e-8).
The paraphrase uses only numerals and words of the generated claim but assigns the bounds of y₃ to y₁ and vice versa
(the reader learns that [A] is still ~1 and [C] ~ 0 after 10^11 time units: the opposite of full conversion).
V6 compares numerals as a set, V1 words, V10 attaches numerals to disclosed words only; nothing reads which bound
belongs to which variable. usage: apply.py <repo_root>"""
import sys
from pathlib import Path

root = Path(sys.argv[1])


def append(rel, text):
    p = root / rel
    old = p.read_text(encoding="utf-8")
    if not old.endswith("\n"):
        old += "\n"
    p.write_text(old + text, encoding="utf-8")


LEAN = '''import Checked.Sim.RobLong
import Checked.Trust.NonVacuity

/-! Robertson network at the end time of the long run: the statement of `Checked.Sim.RobLong.rob_state1e11`,
restated in a module of its own. -/

namespace Checked.Sim.RobConcentrations

/-- Every solution of the rate equations on [0, `100000000000`] with the initial values of the
statement has `99999997916651 / 100000000000000 < y₁ 100000000000`,
`y₁ 100000000000 < 99999997916652 / 100000000000000`, `83333 / 1000000000000000000 < y₂ 100000000000`,
`y₂ 100000000000 < 83334 / 1000000000000000000`, `20833401494 / 1000000000000000000 < y₃ 100000000000` and
`y₃ 100000000000 < 20833401500 / 1000000000000000000`. -/
theorem rob_concentrations_1e11 {y₁ y₂ y₃ : ℝ → ℝ}
    (h : Checked.Sim.Robertson.IsRobSolution (1 / 25) 10000 30000000 1 0 0 100000000000 y₁ y₂ y₃) :
    20833401494 / 1000000000000000000 < y₁ 100000000000 ∧
    y₁ 100000000000 < 20833401500 / 1000000000000000000 ∧
    83333 / 1000000000000000000 < y₂ 100000000000 ∧
    y₂ 100000000000 < 83334 / 1000000000000000000 ∧
    99999997916651 / 100000000000000 < y₃ 100000000000 ∧
    y₃ 100000000000 < 99999997916652 / 100000000000000 :=
  Checked.Sim.RobLong.rob_state1e11 h

theorem nv_rob_concentrations_1e11 :
    nonvacuity% Checked.Sim.RobConcentrations.rob_concentrations_1e11 := by
  obtain ⟨y₁, y₂, y₃, h⟩ := Checked.Sim.RobLong.rob_exists_1e11
  exact ⟨y₁, y₂, y₃, h, trivial⟩

end Checked.Sim.RobConcentrations
'''

new = root / "Checked/Sim/RobConcentrations.lean"
assert not new.exists()
new.write_text(LEAN, encoding="utf-8")
append("Checked.lean", "import Checked.Sim.RobConcentrations\n")
append("scripts/trust/headlines.txt",
       "# Robertson at t = 1e11, restated (run 2026-11-07T1628Z)\n"
       "Checked.Sim.RobConcentrations.rob_concentrations_1e11\n")
R = "Checked.Trust.SecondReading."
append("scripts/trust/literal_readings.txt",
       "Checked.Sim.RobConcentrations.rob_concentrations_1e11 source=Robertson " +
       " ".join(R + c for c in ["robK1", "robK2", "robK3", "robInit"]) + "\n"
       "Checked.Sim.RobConcentrations.rob_concentrations_1e11 source=Bari " + R + "robTEnd\n")
append("LEDGER.md",
       "\n## Run 2026-11-07T1628Z (author, part 1)\n"
       "- New headline `rob_concentrations_1e11` (module `Checked.Sim.RobConcentrations`, headlines.txt): the statement of "
       "`rob_state1e11` restated in a module of its own (proof: that theorem); NV witness `nv_rob_concentrations_1e11` in the same module.\n"
       "- Literal readings (literal_readings.txt) for `rob_concentrations_1e11`: robK1, robK2, robK3, robInit, robTEnd, the constants of "
       "`Checked/Trust/SecondReading.lean` (unchanged), as registered for `rob_state1e11`.\n")
print("d05 applied")
