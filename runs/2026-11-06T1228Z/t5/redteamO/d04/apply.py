import sys, pathlib
root = pathlib.Path(sys.argv[1])
def rd(rel):
    return (root / rel).read_text(encoding="utf-8")
def rep(rel, old, new):
    p = root / rel; t = p.read_text(encoding="utf-8")
    assert t.count(old) == 1, (rel, old)
    p.write_text(t.replace(old, new), encoding="utf-8")
def app(rel, s):
    p = root / rel; t = p.read_text(encoding="utf-8")
    if not t.endswith("\n"): t += "\n"
    p.write_text(t + s, encoding="utf-8")
def new(rel, s):
    p = root / rel; p.parent.mkdir(parents=True, exist_ok=True)
    assert not p.exists(), rel
    p.write_text(s, encoding="utf-8")
ROB = ("Checked.Trust.SecondReading.robK1 Checked.Trust.SecondReading.robK2 Checked.Trust.SecondReading.robK3 "
       "Checked.Trust.SecondReading.robInit")

LEAN = """import Mathlib.Tactic.NormNum
import Checked.Sim.Robertson
import Checked.Trust.NonVacuity

/-!
# Robertson's stiff network: the intermediate species is small at the end of the run

A one-line consequence of `Checked.Sim.Robertson.rob_state40`.
-/

namespace Checked.Sim.RobBelow

/-- Robertson's stiff network, intermediate species B: every solution of the rate equations on [0, 40]
with k₁ = 1/25, k₂ = 10⁴, k₃ = 3·10⁷ and initial concentrations (1, 0, 0) has y₂(40) < 1/100000, so B
stays below 10⁻⁵ during the run. -/
theorem rob_b_small {y₁ y₂ y₃ : ℝ → ℝ}
    (h : Checked.Sim.Robertson.IsRobSolution (1 / 25) 10000 30000000 1 0 0 40 y₁ y₂ y₃) :
    y₂ 40 < 1 / 100000 := by
  have h1 := (Checked.Sim.Robertson.rob_state40 h).2.2.2.1
  exact lt_trans h1 (by norm_num)

end Checked.Sim.RobBelow

namespace Checked.Trust.NV
theorem rob_b_small : nonvacuity% Checked.Sim.RobBelow.rob_b_small := by
  obtain ⟨y₁, y₂, y₃, h⟩ := Checked.Sim.Robertson.rob_exists
  exact ⟨y₁, y₂, y₃, h, trivial⟩
end Checked.Trust.NV
"""
new("Checked/Sim/RobBelow.lean", LEAN)
app("Checked.lean", "import Checked.Sim.RobBelow\n")
H = "Checked.Sim.RobBelow.rob_b_small"
app("scripts/trust/headlines.txt", H + "\n")
app("scripts/trust/literal_readings.txt", H + " source=Robertson " + ROB + " Checked.Trust.SecondReading.robT\n")
app("LEDGER.md", "\n- 2026-11-06T1228Z: **Literal reading** for `rob_b_small` (literal_readings.txt, source=Robertson): `Checked.Trust.SecondReading.robK1`, `robK2`, `robK3`, `robInit`, `robT` (the same blind reader constants as `rob_state40`). New headline `rob_b_small` (Checked/Sim/RobBelow.lean); frozen.txt relocked (new entries only).\n")
