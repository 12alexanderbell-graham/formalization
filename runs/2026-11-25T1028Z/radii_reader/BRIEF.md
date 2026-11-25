# Blind literal reading brief (run 2026-11-25T1028Z): growth of consecutive turning radii of the isothermal-sphere branch parameter

Do NOT read anything in the repository except this brief (no `Checked/`, `Work/`, other `runs/` folders, other `*.md` files, git history). Write only to `runs/2026-11-25T1028Z/radii_reader/`. Do not compile Lean. You may run your own Python in a temporary directory outside the repository. arXiv: arxiv.org/pdf only, never ar5iv or e-print.

Physics: the regular solution w of w'' + (2/s) w' + e^w = 0, w(0) = 0 (the isothermal sphere, equivalently radial solutions of the Gelfand problem in the 3-D ball), and the branch parameter λ(s) = s² e^{w(s)}. λ rises from 0 to a first maximum, then oscillates with turning points of alternating type (maximum, minimum, maximum, …) and tends to the value λ_∞ it has along the singular solution w = log(λ_∞ / s²). The turning points are numbered as one sequence ζ indexed by the natural numbers 0, 1, 2, …, in increasing order of radius, starting with the first maximum (ζ 0).

The claims being checked:
1. The quotient of the next turning radius over the current one, ζ_{k+1}/ζ_k, tends as k → ∞ to the exponential of (a positive integer B) times π over the square root of a positive integer N (both produced by the linearisation of the equation about the singular solution). Determine B and N yourself.
2. Explicit bounds on that quotient (some lower bound `lo`, left as a variable) hold for every k from the index of the SEVENTH turning point on (counting the first maximum as the first turning point); M is that index in the numbering of ζ.
3. The deviation quotient: the deviation of λ from λ_∞ at the next turning point over the deviation at the current one, written with λ(s) = s ^ P * exp(w s) for the integer exponent P.

Fill in the capital placeholders A, B, N, M, P and C in this Lean template — keep every other character, including the import lines, the `open` line, the doc comments and the line breaks, exactly as written — and write it to `runs/2026-11-25T1028Z/radii_reader/SecondReadingGelfandTurnRadii.lean`:

```lean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
/-! Blind literal reading for the growth of consecutive turning radii of the radial Gelfand branch (run 2026-11-25T1028Z). -/
namespace Checked.Trust.SecondReading
open Filter Topology
/-- Radial Gelfand problem (isothermal sphere): the quotient of the next turning radius over the current one tends to the exponential of an integer times pi over the square root of the integer of the linearisation. -/
def gelfandTurnRadii (ζ : ℕ → ℝ) : Prop :=
  Tendsto (fun k : ℕ => ζ (k + A) / ζ k) atTop (𝓝 (Real.exp (B * Real.pi / Real.sqrt N)))
/-- Radial Gelfand problem: a lower bound `lo` on the quotient of consecutive turning radii from the seventh turning point on. -/
def gelfandRadiiFrom (ζ : ℕ → ℝ) (lo : ℝ) : Prop :=
  ∀ k : ℕ, M ≤ k → lo ≤ ζ (k + A) / ζ k
/-- Radial Gelfand problem: the quotient of the deviations of the branch parameter from its value along the singular solution at the next and at the current turning point. -/
noncomputable def gelfandDevQuot (w : ℝ → ℝ) (ζ : ℕ → ℝ) (k : ℕ) : ℝ :=
  (ζ (k + A) ^ P * Real.exp (w (ζ (k + A))) - C) / (ζ k ^ P * Real.exp (w (ζ k)) - C)
end Checked.Trust.SecondReading
```

- A: a natural-number literal, the step in the index from the current turning point to the next one.
- B: a real literal (an integer), the integer factor of π in the limit.
- N: a real literal (an integer), the integer under the square root.
- M: a natural-number literal, the index in ζ of the seventh turning point.
- P: a natural-number literal, the power of s in λ.
- C: a real literal, the value λ_∞.

Also write `notes.md` in the same folder: your reasoning in a few lines and anything you were unsure of. Report both files' contents in your final message.
