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
import Checked.Sim.RobLong
import Checked.Trust.NonVacuity

/-!
# Robertson's stiff network: the Bari reference value of the third concentration at t = 10¹¹

A one-line consequence of `Checked.Sim.RobLong.rob_printed_y3_low`: the lower bound of that theorem,
weakened by a margin.
-/

namespace Checked.Sim.RobNear

/-- The printed reference value 0.9999999791665050 of the Bari IVP test set for the third concentration of
Robertson's network at t = 10¹¹ is reproduced to within 10⁻⁹: every solution of the rate equations on
[0, 10¹¹] with k₁ = 1/25, k₂ = 10⁴, k₃ = 3·10⁷ and initial concentrations (1, 0, 0) has y₃(10¹¹) within
10⁻⁹ of it. -/
theorem rob_y3_near_printed {y₁ y₂ y₃ : ℝ → ℝ}
    (h : Checked.Sim.Robertson.IsRobSolution (1 / 25) 10000 30000000 1 0 0 100000000000 y₁ y₂ y₃) :
    9999999791665050 / 10000000000000000 - 1 / 1000000000 < y₃ 100000000000 := by
  have h1 := Checked.Sim.RobLong.rob_printed_y3_low h
  have h2 : (9999999791665050 / 10000000000000000 : ℝ) - 1 / 1000000000 <
      9999999791665050 / 10000000000000000 + 1 / 100000000000000 := by norm_num
  exact lt_trans h2 h1

end Checked.Sim.RobNear

namespace Checked.Trust.NV
theorem rob_y3_near_printed : nonvacuity% Checked.Sim.RobNear.rob_y3_near_printed := by
  obtain ⟨y₁, y₂, y₃, h⟩ := Checked.Sim.RobLong.rob_exists_1e11
  exact ⟨y₁, y₂, y₃, h, trivial⟩
end Checked.Trust.NV
"""
new("Checked/Sim/RobNear.lean", LEAN)
app("Checked.lean", "import Checked.Sim.RobNear\n")
app("scripts/trust/headlines.txt", "Checked.Sim.RobNear.rob_y3_near_printed\n")
H = "Checked.Sim.RobNear.rob_y3_near_printed"
app("scripts/trust/literal_readings.txt",
    H + " source=Robertson " + ROB + "\n" +
    H + " source=Bari Checked.Trust.SecondReading.robTEnd Checked.Trust.SecondReading.robY3Ref\n")
app("LEDGER.md", "\n- 2026-11-06T1228Z: **Literal reading** for `rob_y3_near_printed` (literal_readings.txt, source=Robertson: `Checked.Trust.SecondReading.robK1`, `robK2`, `robK3`, `robInit`; source=Bari: `Checked.Trust.SecondReading.robTEnd`, `robY3Ref`; the same blind reader constants as `rob_printed_y3_low`). New headline `rob_y3_near_printed` (Checked/Sim/RobNear.lean); frozen.txt relocked (new entries only).\n")
