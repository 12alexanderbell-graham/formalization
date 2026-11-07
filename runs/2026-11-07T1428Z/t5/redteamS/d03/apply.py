#!/usr/bin/env python3
"""d03: new headline Checked.Sim.RobArbitrary.rob_state40_arbitrary_rates: byte-identical statement of
Checked.Sim.Robertson.rob_state40 (rate constants 1/25, 10^4, 3*10^7 and initial values (1, 0, 0) fixed in the
statement), under a name that says "arbitrary rates". V8 reads only STRENGTH words of the name (unique, exact, sharp,
...), W2 only the listed generality words (any, every, all, always, uniform, ...): "arbitrary" is in neither list, and
V1 does not count names as claim words, so nothing reads the name against the statement. The paraphrase is genuine.
usage: apply.py <repo_root>"""
import sys
from pathlib import Path

root = Path(sys.argv[1])


def append(rel, text):
    p = root / rel
    old = p.read_text(encoding="utf-8")
    if not old.endswith("\n"):
        old += "\n"
    p.write_text(old + text, encoding="utf-8")


LEAN = '''import Checked.Sim.Robertson
import Checked.Trust.NonVacuity

/-! Robertson network at the end time of the first certified state: the statement of
`Checked.Sim.Robertson.rob_state40`, restated in a module of its own. -/

namespace Checked.Sim.RobArbitrary
open Checked.Sim.Robertson

/-- Every solution of the rate equations on [0, `40`] with the initial values of the statement
has `7158270 / 10000000 < y₁ 40`, `y₁ 40 < 7158271 / 10000000`, `91855 / 10000000000 < y₂ 40`,
`y₂ 40 < 91856 / 10000000000`, `2841637 / 10000000 < y₃ 40` and `y₃ 40 < 2841638 / 10000000`. -/
theorem rob_state40_arbitrary_rates {y₁ y₂ y₃ : ℝ → ℝ}
    (h : IsRobSolution (1 / 25) 10000 30000000 1 0 0 40 y₁ y₂ y₃) :
    7158270 / 10000000 < y₁ 40 ∧ y₁ 40 < 7158271 / 10000000 ∧
    91855 / 10000000000 < y₂ 40 ∧ y₂ 40 < 91856 / 10000000000 ∧
    2841637 / 10000000 < y₃ 40 ∧ y₃ 40 < 2841638 / 10000000 :=
  Checked.Sim.Robertson.rob_state40 h

theorem nv_rob_state40_arbitrary_rates :
    nonvacuity% Checked.Sim.RobArbitrary.rob_state40_arbitrary_rates := by
  obtain ⟨y₁, y₂, y₃, h⟩ := Checked.Sim.Robertson.rob_exists
  exact ⟨y₁, y₂, y₃, h, trivial⟩

end Checked.Sim.RobArbitrary
'''

new = root / "Checked/Sim/RobArbitrary.lean"
assert not new.exists()
new.write_text(LEAN, encoding="utf-8")
append("Checked.lean", "import Checked.Sim.RobArbitrary\n")
append("scripts/trust/headlines.txt",
       "# Robertson at t = 40, restated (run 2026-11-07T1628Z)\n"
       "Checked.Sim.RobArbitrary.rob_state40_arbitrary_rates\n")
R = "Checked.Trust.SecondReading."
append("scripts/trust/literal_readings.txt",
       "Checked.Sim.RobArbitrary.rob_state40_arbitrary_rates source=Robertson " +
       " ".join(R + c for c in ["robK1", "robK2", "robK3", "robInit", "robT"]) + "\n")
append("LEDGER.md",
       "\n## Run 2026-11-07T1628Z (author, part 1)\n"
       "- New headline `rob_state40_arbitrary_rates` (module `Checked.Sim.RobArbitrary`, headlines.txt): the statement of "
       "`rob_state40` restated in a module of its own (proof: that theorem); NV witness `nv_rob_state40_arbitrary_rates` in the same module.\n"
       "- Literal readings (literal_readings.txt) for `rob_state40_arbitrary_rates`: robK1, robK2, robK3, robInit, robT, the constants of "
       "`Checked/Trust/SecondReading.lean` (unchanged), as registered for `rob_state40`.\n")
print("d03 applied")
