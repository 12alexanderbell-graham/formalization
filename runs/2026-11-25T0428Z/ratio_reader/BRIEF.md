# Blind literal reading brief (run 2026-11-25T0428Z): the limit of the quotient of consecutive turning-value deviations of the isothermal-sphere branch parameter

Do NOT read anything in the repository except this brief (no `Checked/`, `Work/`, other `runs/` folders, other `*.md` files, git history). Write only to `runs/2026-11-25T0428Z/ratio_reader/`. Do not compile Lean. You may run your own Python in a temporary directory outside the repository. arXiv: arxiv.org/pdf only, never ar5iv or e-print.

Physics: the regular solution w of w'' + (2/s) w' + e^w = 0, w(0) = 0 (the isothermal sphere, equivalently radial solutions of the Gelfand problem in the 3-D ball), and the branch parameter λ(s) = s² e^{w(s)}. λ rises from 0 to a first maximum, then oscillates with turning points of alternating type (maximum, minimum, maximum, …) and tends to the value λ_∞ it has along the singular solution w = log(λ_∞ / s²). The turning points are numbered as one sequence ζ indexed by the natural numbers 0, 1, 2, …, in increasing order of radius, starting with the first maximum.

The claim being checked: the quotient of the deviation of λ from λ_∞ at the next turning point over the deviation at the current one, (λ(ζ_{k+1}) − λ_∞)/(λ(ζ_k) − λ_∞), tends, as k tends to infinity, to minus the exponential of minus π over the square root of a positive integer N (the integer that the linearisation of the equation about the singular solution produces). Determine N yourself (from the linearisation, by computation, or both).

Fill in the capital placeholders A, B and N in this Lean template — keep every other character, including the import line, the `open` line, the doc comments and the line breaks, exactly as written — and write it to `runs/2026-11-25T0428Z/ratio_reader/SecondReadingGelfandTurnRatio.lean`:

```lean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
/-! Blind literal reading for the limit of the quotient of consecutive turning-value deviations of the radial Gelfand branch (run 2026-11-25T0428Z). -/
namespace Checked.Trust.SecondReading
open Filter Topology
/-- Radial Gelfand problem (isothermal sphere): the quotient of the deviations of the branch parameter from its value along the singular solution at the next and at the current turning point tends to minus the exponential of minus pi over the square root of the integer of the linearisation. -/
def gelfandTurnRatio (w : ℝ → ℝ) (ζ : ℕ → ℝ) : Prop :=
  Tendsto (fun k : ℕ => (ζ (k + A) ^ 2 * Real.exp (w (ζ (k + A))) - B) /
    (ζ k ^ 2 * Real.exp (w (ζ k)) - B)) atTop (𝓝 (-Real.exp (-(Real.pi / Real.sqrt N))))
end Checked.Trust.SecondReading
```

- A: a natural-number literal, the step in the index from the current turning point to the next one.
- B: a real literal, the value λ_∞.
- N: a real literal (an integer), the integer under the square root.

Also write `notes.md` in the same folder: your reasoning in a few lines and anything you were unsure of. Report both files' contents in your final message.
