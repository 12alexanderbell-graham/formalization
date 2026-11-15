# Blind literal reading brief: the singular value of the Gelfand parameter in the three-dimensional ball

Do NOT read anything in the repository except this brief (no `Checked/`, `Work/`, other `runs/` folders, other `*.md` files, git history). Write only into the folder that contains this brief. Do not compile Lean. Derive the value yourself from the description below; you may run your own Python (sympy/numpy/mpmath) in a temporary directory outside the repository to check it. If a web tool fails, is blocked or times out, record the source as "not read"; never fetch the same content with curl, wget or code. arXiv: arxiv.org/pdf only, never ar5iv or e-print.

Mathematics: the Gelfand (Bratu) problem Δu + λ e^u = 0 in the unit ball of three-dimensional space, u = 0 on the boundary sphere, λ > 0 a parameter. Besides the bounded radial solutions there is, for exactly one value of λ, a radial solution that is unbounded at the centre (it behaves like a multiple of log r as r → 0, satisfies the equation for 0 < r ≤ 1 and vanishes at r = 1). The bounded radial branch oscillates around that value of λ.

Fill in the capital placeholder A in this Lean template — keep every other character, including the import line, the doc comments and the line breaks, exactly as written — and write it as `SecondReadingGelfandExtrema.lean` in this brief's folder:

```lean
import Mathlib.Data.Real.Basic
/-! Blind literal reading for the turning points of the radial Gelfand branch in the three-dimensional ball. -/
namespace Checked.Trust.SecondReading
/-- Gelfand problem in the three-dimensional unit ball: the value of the parameter λ at which the problem has its singular radial solution (unbounded at the centre). -/
noncomputable def gelfandSingularLambda : ℝ := A
end Checked.Trust.SecondReading
```

- A: that value of λ, as an exact natural-number literal (or an exact fraction `p / q` of natural-number literals if it is not an integer).

Also write `notes.md` in the same folder: your derivation in a few lines (find the singular solution explicitly and check it), and anything you were unsure of. Report both files' contents in your final message.
