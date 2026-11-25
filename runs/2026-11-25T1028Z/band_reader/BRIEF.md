# Blind literal reading brief (run 2026-11-25T1028Z): a two-sided band on the quotient of consecutive turning radii of the isothermal-sphere branch parameter

Do NOT read anything in the repository except this brief (no `Checked/`, `Work/`, other `runs/` folders, other `*.md` files, git history). Write only to `runs/2026-11-25T1028Z/band_reader/`. Do not compile Lean.

Physics: the regular solution w of w'' + (2/s) w' + e^w = 0, w(0) = 0 (the isothermal sphere, equivalently radial solutions of the Gelfand problem in the 3-D ball), and the branch parameter λ(s) = s² e^{w(s)}. λ rises from 0 to a first maximum, then oscillates with turning points of alternating type (maximum, minimum, maximum, …). The turning points are numbered as one sequence ζ indexed by the natural numbers 0, 1, 2, …, in increasing order of radius, starting with the first maximum (ζ 0).

The claim being checked: at a turning point with index k, the quotient of the radius of the NEXT turning point over the radius of the current one lies between a lower bound `lo` and an upper bound `hi` (both left as variables).

Fill in the capital placeholder A in this Lean template — keep every other character, including the import line, the doc comments and the line breaks, exactly as written — and write it to `runs/2026-11-25T1028Z/band_reader/SecondReadingGelfandRadiiBand.lean`:

```lean
import Mathlib.Data.Real.Basic
/-! Blind literal reading for a two-sided band on the quotient of consecutive turning radii of the radial Gelfand branch (run 2026-11-25T1028Z). -/
namespace Checked.Trust.SecondReading
/-- Radial Gelfand problem: the quotient of the next turning radius over the current one lies between `lo` and `hi`. -/
def gelfandRadiiBand (ζ : ℕ → ℝ) (k : ℕ) (lo hi : ℝ) : Prop :=
  lo ≤ ζ (k + A) / ζ k ∧ ζ (k + A) / ζ k ≤ hi
end Checked.Trust.SecondReading
```

- A: a natural-number literal, the step in the index from the current turning point to the next one.

Also write `notes.md` in the same folder: your reasoning in a line or two and anything you were unsure of. Report both files' contents in your final message.
