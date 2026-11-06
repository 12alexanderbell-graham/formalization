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

LEAN = "import Mathlib.Analysis.Calculus.Deriv.Abs\n\n/-!\n# The derivative of the absolute value at the origin\n\nA kink of a potential well, stated with Mathlib's `deriv`.\n-/\n\nnamespace Checked.Math.AbsKink\n\n/-- The derivative of the function |x| at the point 0 equals 0. -/\ntheorem deriv_abs_at_zero : deriv (fun x : ℝ => |x|) 0 = 0 := deriv_abs_zero\n\nend Checked.Math.AbsKink\n"
wr('Checked/Math/AbsKink.lean', LEAN)
app("Checked.lean", "import Checked.Math.AbsKink\n")
app("scripts/trust/headlines.txt", 'Checked.Math.AbsKink.deriv_abs_at_zero' + "\n")
