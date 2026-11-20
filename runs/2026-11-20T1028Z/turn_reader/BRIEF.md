# Blind literal reading brief (run 2026-11-20T1028Z): the turning points of the isothermal-sphere branch parameter, by position in their sequence

Do NOT read anything in the repository except this brief (no `Checked/`, `Work/`, other `runs/` folders, other `*.md` files, git history). Write only to `runs/2026-11-20T1028Z/turn_reader/`. Do not compile Lean. You may run your own Python in a temporary directory outside the repository. arXiv: arxiv.org/pdf only, never ar5iv or e-print.

Physics: the regular solution w of w'' + (2/s) w' + e^w = 0, w(0) = 0 (the isothermal sphere, equivalently radial solutions of the Gelfand problem in the 3-D ball), and the branch parameter λ(s) = s² e^{w(s)}. λ rises from 0 to a first maximum, then oscillates with turning points of alternating type (maximum, minimum, maximum, …) and tends to 2.

The claim being checked numbers all turning points of λ as one sequence ζ indexed by the natural numbers 0, 1, 2, …, in increasing order of radius, starting with the first maximum, and states windows for λ at the second, third and fourth turning points of λ (counting the first maximum as the first).

Fill in the capital placeholders A, B, C in this Lean template — keep every other character, including the import line, the doc comments and the line breaks, exactly as written — and write it to `runs/2026-11-20T1028Z/turn_reader/SecondReadingGelfandTurns.lean`:

```lean
import Mathlib.Data.Real.Basic
/-! Blind literal reading for the turning values of the radial Gelfand branch (run 2026-11-20T1028Z). -/
namespace Checked.Trust.SecondReading
/-- Radial Gelfand problem (isothermal sphere): the radius, in the sequence ζ of turning points of the branch parameter, of the second turning point (the first minimum). -/
def gelfandSecondTurn (ζ : ℕ → ℝ) : ℝ := ζ A
/-- Radial Gelfand problem (isothermal sphere): the radius, in the sequence ζ of turning points of the branch parameter, of the third turning point (the second maximum). -/
def gelfandThirdTurn (ζ : ℕ → ℝ) : ℝ := ζ B
/-- Radial Gelfand problem (isothermal sphere): the radius, in the sequence ζ of turning points of the branch parameter, of the fourth turning point (the second minimum). -/
def gelfandFourthTurn (ζ : ℕ → ℝ) : ℝ := ζ C
end Checked.Trust.SecondReading
```

- A, B, C: natural-number literals, the index in the sequence described above.

Also write `notes.md` in the same folder: your reasoning in a few lines (optionally a numerical check of the first four turning points of λ) and anything you were unsure of. Report both files' contents in your final message.
