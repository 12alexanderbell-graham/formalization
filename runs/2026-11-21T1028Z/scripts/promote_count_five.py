"""Checked copy of Work.Math.GelfandPDECountTurningValuesFive (statement, docstring and proof unchanged)."""
src = open("Work/Math/GelfandPDECountTurningValuesFive.lean").read()
head, rest = src.split("namespace Work.Math.GelfandPDECountTurningValuesFive\n", 1)
assert head.startswith("import Mathlib\n")
newhead = ("import Checked.Math.GelfandPDECountTurningMain\nimport Checked.Math.GelfandTurningValuesFive\n\n"
  "/-! Gelfand problem in the three-dimensional ball as a PDE, `GelfandPDECountTurningValuesFive`: the number of radial "
  "classical solutions for every positive parameter, as in `Checked.Math.GelfandPDECountTurning`, with the value of the "
  "branch parameter at its fourth and fifth turning points enclosed as well. Promoted from "
  "`Work/Math/GelfandPDECountTurningValuesFive.lean` (frozen, proved and audited by run 2026-11-21T1028Z); the route is "
  "`Checked.Math.GelfandPDECountTurningMain.cset_encard` and `Checked.Math.BonnorEbertCountMain.count_abstract` applied "
  "to the turning sequence of `Checked.Math.GelfandTurningValuesFive.gelfand_turning_values_five`. -/\n\n")
rest = rest.replace("end Work.Math.GelfandPDECountTurningValuesFive\n", "end Checked.Math.GelfandPDECountTurningValuesFive\n")
assert rest.count("end Checked.Math.GelfandPDECountTurningValuesFive\n") == 1
open("Checked/Math/GelfandPDECountTurningValuesFive.lean", "w").write(
    newhead + "namespace Checked.Math.GelfandPDECountTurningValuesFive\n" + rest)
