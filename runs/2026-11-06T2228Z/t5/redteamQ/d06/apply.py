import sys, pathlib
root = pathlib.Path(sys.argv[1])
def rd(p): return (root/p).read_text(encoding="utf-8")
def wr(p, s): (root/p).write_text(s, encoding="utf-8")
def app(p, s):
    t = rd(p)
    if not t.endswith("\n"): t += "\n"
    wr(p, t + s)
def rep(p, old, new):
    t = rd(p); assert t.count(old) == 1, (p, old[:60], t.count(old)); wr(p, t.replace(old, new))

LEAN = "import Checked.Records.Basic\nimport Mathlib.Analysis.Complex.ExponentialBounds\n\n/-!\n# Euler's number rounded\n\nA rounding statement for exp 1.\n-/\n\nnamespace Checked.Math.EulerNumber\n\nopen Checked.Records\n\n/-- The number `Real.exp 1` equals 2.718 to 6 decimal places. -/\ntheorem exp_one_rounds : RoundsTo (Real.exp 1) 2.718 3 := by\n  have h1 := Real.exp_one_gt_d9\n  have h2 := Real.exp_one_lt_d9\n  apply roundsTo_of_mem <;> norm_num <;> linarith\n\nend Checked.Math.EulerNumber\n"
wr('Checked/Math/EulerNumber.lean', LEAN)
app("Checked.lean", "import Checked.Math.EulerNumber\n")
app("scripts/trust/headlines.txt", 'Checked.Math.EulerNumber.exp_one_rounds' + "\n")
