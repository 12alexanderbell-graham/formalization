"""Freeze of gelfand_pde_radial_count_turning_values_five from the parent's freeze (asserted replacements)."""
import subprocess, sys
src = subprocess.run(["git", "show", "0316b539:Work/Math/GelfandPDECountTurningValues.lean"],
                     capture_output=True, text=True, check=True).stdout
reps = [
    ("import Checked.Math.GelfandTurningValues\n", "import Checked.Math.GelfandTurningValuesFive\n"),
    ("`GelfandPDECountTurningValues`: the number of radial\nclassical solutions for every positive parameter, as in `Checked.Math.GelfandPDECountTurning`, with the value of the\nbranch parameter at its fourth turning point enclosed as well (FROZEN by run 2026-11-20T1628Z before its proof).",
     "`GelfandPDECountTurningValuesFive`: the number of radial\nclassical solutions for every positive parameter, as in `Checked.Math.GelfandPDECountTurning`, with the value of the\nbranch parameter at its fourth and fifth turning points enclosed as well (FROZEN by run 2026-11-21T1028Z before its proof)."),
    ("`Checked.Math.GelfandTurningValues.gelfand_turning_values`. -/", "`Checked.Math.GelfandTurningValuesFive.gelfand_turning_values_five`. -/"),
    ("namespace Work.Math.GelfandPDECountTurningValues\n", "namespace Work.Math.GelfandPDECountTurningValuesFive\n"),
    ("end Work.Math.GelfandPDECountTurningValues\n", "end Work.Math.GelfandPDECountTurningValuesFive\n"),
    ("and 2.10858, `lamT 3` between 1.9637 and 1.9707, `lamT (2 * k)`",
     "and 2.10858, `lamT 3` between 1.967422 and 1.967510, `lamT 4` between 2.009926 and 2.010028, `lamT (2 * k)`"),
    ("theorem gelfand_pde_radial_count_turning_values :", "theorem gelfand_pde_radial_count_turning_values_five :"),
    ("      1.9637 ≤ lamT 3 ∧ lamT 3 ≤ 1.9707 ∧\n",
     "      1.967422 ≤ lamT 3 ∧ lamT 3 ≤ 1.967510 ∧ 2.009926 ≤ lamT 4 ∧ lamT 4 ≤ 2.010028 ∧\n"),
]
for a, b in reps:
    assert src.count(a) == 1, a
    src = src.replace(a, b)
open(sys.argv[1], "w").write(src)
