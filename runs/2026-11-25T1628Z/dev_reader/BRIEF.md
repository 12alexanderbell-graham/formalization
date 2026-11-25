# Blind literal reading brief (run 2026-11-25T1628Z): the damping of the Bonnor–Ebert mass extrema

Do NOT read anything in the repository except this brief (no `Checked/`, `Work/`, other `runs/` folders, other `*.md` files, git history). Write only to `runs/2026-11-25T1628Z/dev_reader/`. Do not compile Lean. You may run your own Python in a temporary directory outside the repository. arXiv: arxiv.org/pdf only, never ar5iv or e-print.

Physics: the isothermal sphere. Let w be the regular solution of w'' + (2/s) w' + e^w = 0, w(0) = 0, with derivative φ = w' (so φ < 0 for s > 0). In these dimensionless units the pressure-confined (Bonnor–Ebert) mass inside radius s is m(s) = s^P (−φ(s)) e^{w(s)/D} / √(F π), with integers P, D, F to be determined by you from the standard definition (the mass is the integral of the density e^w over the ball of radius s, divided by the square root of the pressure e^w at s, with the normalisation by √(4π) of the Bonnor–Ebert literature: m(s) = M √(4π... )/... — work it out so that the mass of the singular isothermal sphere w = log(2/s²) is a constant). m(s) rises to a first maximum, then oscillates with extrema of alternating type (maximum, minimum, maximum, …) and tends to the mass √(G / π) of the singular isothermal sphere (G an integer to be determined by you from that solution). The extrema are numbered as one sequence ξ indexed by the natural numbers 0, 1, 2, …, in increasing order of radius, starting with the first maximum (ξ 0).

The claim being checked: the deviation of the mass from the singular value at the next extremum, divided by the deviation at the current one, tends as k → ∞ to minus the exponential of minus π over the square root of a positive integer N produced by the linearisation of the equation about the singular solution. Determine N yourself.

Fill in the capital placeholders A, P, D, F, G and N in this Lean template — keep every other character, including the import lines, the `open` line, the doc comments and the line breaks, exactly as written — and write it to `runs/2026-11-25T1628Z/dev_reader/SecondReadingBETurnRatio.lean`:

```lean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
/-! Blind literal reading for the limit of the quotient of consecutive deviations of the Bonnor–Ebert mass at its extrema (run 2026-11-25T1628Z). -/
namespace Checked.Trust.SecondReading
open Filter Topology
/-- Bonnor–Ebert sphere: the quotient of the deviations of the pressure-confined mass from the value of the singular isothermal sphere at the next and at the current extremum tends to minus the exponential of minus pi over the square root of the integer of the linearisation. -/
def beTurnRatio (w φ : ℝ → ℝ) (ξ : ℕ → ℝ) : Prop :=
  Tendsto (fun k : ℕ =>
    (ξ (k + A) ^ P * (-φ (ξ (k + A))) * Real.exp (w (ξ (k + A)) / D) / Real.sqrt (F * Real.pi) -
        Real.sqrt (G / Real.pi)) /
      (ξ k ^ P * (-φ (ξ k)) * Real.exp (w (ξ k) / D) / Real.sqrt (F * Real.pi) -
        Real.sqrt (G / Real.pi))) atTop (𝓝 (-Real.exp (-(Real.pi / Real.sqrt N))))
end Checked.Trust.SecondReading
```

- A: a natural-number literal, the step in the index from the current extremum to the next one.
- P: a natural-number literal, the power of s in m.
- D: a real literal (an integer), the divisor of w in the exponent.
- F: a real literal (an integer), the factor of π under the square root of the normalisation.
- G: a real literal (an integer), with √(G/π) the mass of the singular isothermal sphere.
- N: a real literal (an integer), the integer under the square root in the limit.

Also write `notes.md` in the same folder: your reasoning in a few lines and anything you were unsure of. Report both files' contents in your final message.
