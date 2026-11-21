"""Freeze of gelfand_turning_values_seven from the freeze 07b6f56 of gelfand_turning_values_five (asserted replacements)."""
import subprocess, sys
src = subprocess.run(["git", "show", "07b6f56:Work/Math/GelfandTurningValuesFive.lean"], capture_output=True, text=True, check=True).stdout
reps = [
 ("`GelfandTurningValuesFive`: the turning sequence", "`GelfandTurningValuesSeven`: the turning sequence"),
 ("at its first five turning points (the five values of the conclusion). Frozen by run 2026-11-21T0428Z before its proof; the planned route is `Checked.Math.GelfandExtremaMain.main`, `Checked.Math.GLamBands.bands` and `Work.Math.GelfandLam4.lam34_band`. -/",
  "at its first seven turning points (the seven values of the conclusion). Frozen by run 2026-11-21T1028Z before its proof; the planned route is `Checked.Math.GelfandExtremaMain.main`, `Checked.Math.GLamBands.bands` and `Work.Math.GelfandLam6.lam3456_band`. -/"),
 ("namespace Work.Math.GelfandTurningValuesFive", "namespace Work.Math.GelfandTurningValuesSeven"),
 ("end Work.Math.GelfandTurningValuesFive", "end Work.Math.GelfandTurningValuesSeven"),
 ("λ(ζ(3)) between 1.967422 and 1.967510 and λ(ζ(4)) between 2.009926 and 2.010028, such that",
  "λ(ζ(3)) between 1.967422 and 1.967510, λ(ζ(4)) between 2.009926 and 2.010028, λ(ζ(5)) between 1.996901 and 1.997023\nand λ(ζ(6)) between 2.000873 and 2.000980, such that"),
 ("theorem gelfand_turning_values_five", "theorem gelfand_turning_values_seven"),
 ("      2.009926 ≤ ζ 4 ^ 2 * Real.exp (w (ζ 4)) ∧ ζ 4 ^ 2 * Real.exp (w (ζ 4)) ≤ 2.010028 ∧\n",
  "      2.009926 ≤ ζ 4 ^ 2 * Real.exp (w (ζ 4)) ∧ ζ 4 ^ 2 * Real.exp (w (ζ 4)) ≤ 2.010028 ∧\n"
  "      1.996901 ≤ ζ 5 ^ 2 * Real.exp (w (ζ 5)) ∧ ζ 5 ^ 2 * Real.exp (w (ζ 5)) ≤ 1.997023 ∧\n"
  "      2.000873 ≤ ζ 6 ^ 2 * Real.exp (w (ζ 6)) ∧ ζ 6 ^ 2 * Real.exp (w (ζ 6)) ≤ 2.000980 ∧\n"),
]
for a, b in reps:
    assert src.count(a) == 1, a
    src = src.replace(a, b)
open(sys.argv[1], "w").write(src)
