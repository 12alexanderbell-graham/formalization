# Brief: blind literal reading for the multiplicity of radial solutions of the Gelfand problem in the unit ball

You are an independent reader. Do not read anything in the repository except this brief and the output path below; in particular never open `Checked/`, `Work/`, other `runs/` folders, `scripts/`, `validation/`, `.lake/` or any other `*.md` file, and do not use git to look at history. Write only into the folder that contains this brief.

## The problem

The Gelfand (Liouville–Bratu–Gelfand, Frank-Kamenetskii) problem in a sphere: Δu + λ e^u = 0 in the open unit ball B centred at the origin of three-dimensional Euclidean space, u = 0 on the boundary sphere, λ a real parameter. Radial solutions u(x) = g(|x|) exist only for λ up to a critical value λ* (the Frank-Kamenetskii parameter of the sphere). Besides the bounded radial solutions there is, for exactly one value S of λ, a radial solution that is unbounded at the centre (it behaves like a multiple of log r as r → 0, satisfies the equation for 0 < r ≤ 1 and vanishes at r = 1). The number of bounded radial solutions is infinite at λ = S, large for λ near S, and at least two for λ from S up to (not including) λ*.

Your jobs:
1. **Read the setting:** the dimension D of the space and the coordinate value C of the centre of the ball (one numeral, as it stands in `u C`, the value of a function u at the centre).
2. **Derive S** yourself: find the singular radial solution explicitly and check it.
3. **Compute λ\* yourself** (do not look it up): radial solutions are u(r) = w(k r) − w(k) with k > 0, where w solves w'' + (2/s) w' + e^w = 0, w(0) = 0, w'(0) = 0 (derive this yourself and check it), and λ = k² e^{w(k)}; λ* is the maximum over s > 0 of s² e^{w(s)}. Integrate with high precision (for example Python `mpmath` with at least 30 significant digits, a Taylor series at s = 0 for a short start, then a high-order method with step-size control), locate the maximiser by solving d/ds [s² e^{w(s)}] = 0, and estimate your error (repeat with another tolerance or method). Scripts and scratch files go to a temporary directory outside the repository (e.g. /tmp/claude-0/many_reader). Web access: a failed, blocked or timed-out WebFetch/WebSearch is recorded as "not read" — never fetch the same content with curl, wget or code; for arXiv only arxiv.org/abs or arxiv.org/pdf, never ar5iv or e-print. Do not take λ* or S from any web page or book.
   Then let `L` be the largest number with exactly nine digits after the decimal point that does not exceed your computed λ* (round down, not to nearest). If your error estimate does not let you decide that ninth digit, say so.

## What to write

ONE Lean 4 file `SecondReadingGelfandMany.lean` in this brief's folder, with exactly this template; replace each capital placeholder by your numeral: `D`, `C` and `S` as plain integer numerals (or `S` as an exact fraction `p / q` of natural-number literals if it is not an integer), `L` your nine-decimal number written as a plain decimal (digits, one point, nine digits). Nothing else changes: keep every other token, the parentheses, the line breaks and the order exactly as shown.

```lean
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
/-! Blind literal reading for the multiplicity of radial solutions of the Gelfand problem in the unit ball (reader: <you>; derivation, computation and sources: <what you used>). -/
namespace Checked.Trust.SecondReading
/-- Gelfand problem in the ball, multiplicity: the equation at a point for the parameter value of the singular radial solution, with Lu the value of the Laplacian of the solution and v the value of the solution at that point. -/
def gelfandManyEqSingular (Lu v : ℝ) : Prop := Lu + S * Real.exp v = 0
/-- Gelfand problem in the ball, multiplicity: the parameter λ is within ε of the parameter value of the singular radial solution. -/
def gelfandManyNearSingular (lam ε : ℝ) : Prop := |lam - S| < ε
/-- Gelfand problem in the ball, multiplicity: if λ is at least the parameter value of the singular radial solution then λ is below the reader's nine-decimal lower rounding of the critical parameter. -/
def gelfandManyTwoRange (lam : ℝ) : Prop := S ≤ lam → lam < L
/-- Gelfand problem in the ball, multiplicity: the values at the centre of the ball of a sequence of functions on the space. -/
def gelfandManyCentreSeq (u : ℕ → EuclideanSpace ℝ (Fin D) → ℝ) : ℕ → ℝ := fun i => u i C
/-- Gelfand problem in the ball, multiplicity: the value of a function on the space at the centre of the ball. -/
def gelfandManyCentre (u : EuclideanSpace ℝ (Fin D) → ℝ) : ℝ := u C
end Checked.Trust.SecondReading
```

Also write `notes.md` in the same folder: your derivations in a few lines, the computation of λ* with its error estimate, and anything you were unsure of. Report both files' contents in your final message.
