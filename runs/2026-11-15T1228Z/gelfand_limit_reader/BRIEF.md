# Blind literal reading brief: the limit of the radial Gelfand branch in the three-dimensional ball

Do NOT read anything in the repository except this brief (no `Checked/`, `Work/`, other `runs/` folders, other `*.md` files, git history). Write only into the folder that contains this brief. Do not compile Lean. Derive the value yourself from the description below; you may run your own Python (scipy/numpy/mpmath) in a temporary directory outside the repository to check it. If a web tool fails, is blocked or times out, record the source as "not read"; never fetch the same content with curl, wget or code. arXiv: arxiv.org/pdf only, never ar5iv or e-print.

Mathematics: the Gelfand (Bratu) problem Δu + λ e^u = 0 in the unit ball of three-dimensional space, u = 0 on the boundary sphere. Its radial solutions are parametrised by the regular solution w of the ODE w'' + (2/s) w' + e^w = 0 with w(0) = 0, w'(0) = 0 (defined for every s ≥ 0): for each s > 0, u(r) = w(s r) − w(s) solves the problem with λ = λ(s) = s² e^{w(s)}. As s tends to infinity, λ(s) converges (oscillating) to a limit, the value of λ at which the problem has a radial solution that is unbounded at the centre.

Fill in the capital placeholder A in this Lean template — keep every other character, including the import lines, the doc comments and the line breaks, exactly as written — and write it as `SecondReadingGelfandLimit.lean` in this brief's folder:

```lean
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Basic
/-! Blind literal reading for the limit of the radial Gelfand branch in the three-dimensional ball. -/
namespace Checked.Trust.SecondReading
open Filter Topology
/-- Gelfand problem in the three-dimensional unit ball: the radial branch parameter λ(s) = s² e^{w(s)} of the regular solution w tends, as s tends to infinity, to the value of the parameter of the singular radial solution. -/
def gelfandBranchLimit (w : ℝ → ℝ) : Prop := Tendsto (fun s => s ^ 2 * Real.exp (w s)) atTop (𝓝 A)
end Checked.Trust.SecondReading
```

- A: the limit, as an exact natural-number literal (or an exact fraction `p / q` of natural-number literals if it is not an integer). Check it two ways: from the explicit singular solution, and numerically (integrate the ODE to large s and look at s² e^{w(s)}).

Also write `notes.md` in the same folder: your derivation in a few lines, the numerical check, and anything you were unsure of. Report both files' contents in your final message.
