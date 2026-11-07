# Brief: blind literal reading of the Gelfand problem in the unit ball as a PDE (run 2026-11-07T0028Z)

You are an independent reader. Do not read anything in /home/claude/formalization except this brief and the output path below; in particular never open `Checked/`, `Work/`, `runs/` (other than this folder), `scripts/`, `validation/`, `.lake/` or any `*.md` there, and do not use git to look at history.

## The problem

The Gelfand (Liouville–Bratu–Gelfand, Frank-Kamenetskii) problem of thermal explosion in a sphere: Δu + λ e^u = 0 in the open unit ball B centred at the origin of three-dimensional Euclidean space, u = 0 on the boundary sphere, λ > 0. A classical solution is twice continuously differentiable in the open ball and continuous up to the boundary. Radial solutions u(x) = g(|x|) exist exactly for λ in an interval (0, λ*], where λ* is the critical (Frank-Kamenetskii) parameter of the sphere.

You have two jobs.

1. **Read the setting.** Write down, as Lean numerals, the dimension of the space, the centre and radius of the ball, and the order of differentiability of a classical solution on the open ball.

2. **Compute λ* yourself.** Do not look the value up; compute it. The standard route: radial solutions are u(r) = w(k r) − w(k) with k > 0, where w(s) solves the Emden–Chandrasekhar initial-value problem w'' + (2/s) w' + e^w = 0, w(0) = 0, w'(0) = 0 (derive this yourself and check it), and then λ = k² e^{w(k)}; λ* is the maximum over s > 0 of s² e^{w(s)}. Integrate with high precision (for example Python `mpmath` with at least 30 significant digits: a Taylor series of w at s = 0 for a short start, then `mpmath.odefun` or a high-order Taylor or Runge–Kutta method with step-size control; or any method you trust), locate the maximiser by solving d/ds [s² e^{w(s)}] = 0, and estimate your error (repeat with a different tolerance or method). Scripts and scratch files go to a temporary directory outside the repository (e.g. /tmp/gelfand_pde_reader). Web access: a failed, blocked or timed-out WebFetch/WebSearch is recorded as "not read" — never fetch the same content with curl, wget or code; for arXiv only arxiv.org/abs or arxiv.org/pdf, never ar5iv or e-print. Do not take λ* from any web page or book: the point is an independent computation.

   Then let `L` be the largest number with exactly nine digits after the decimal point that does not exceed your computed λ* (round down, not to nearest). If your error estimate does not let you decide that ninth digit, say so in the report and the module doc.

## What to write

ONE Lean 4 file `runs/2026-11-07T0028Z/gelfand_pde_reader/SecondReadingGelfandPDE.lean`, with exactly this template; replace each capital placeholder by your numeral: `D` the dimension, `C` the centre's coordinate value (written as one numeral, as it stands inside `(C : EuclideanSpace ...)` and `ball C R`), `R` the radius, `K` the order of differentiability, all plain integer numerals; `L` your nine-decimal number written as a plain decimal (digits, one point, nine digits). Nothing else changes: keep every other token, the parentheses and the order exactly as shown.

```lean
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
/-! Blind literal reading of the Gelfand problem in the unit ball as a PDE (reader: <you>; derivation, computation and sources: <what you used>). -/
namespace Checked.Trust.SecondReading
open Metric
/-- Gelfand problem in the ball as a PDE: the space of the problem, Euclidean space of the problem's dimension. -/
def gelfandPdeSpace : Type := EuclideanSpace ℝ (Fin D)
/-- Gelfand problem in the ball as a PDE: the open ball of the problem (centre, radius). -/
def gelfandPdeBall : Set (EuclideanSpace ℝ (Fin D)) := ball (C : EuclideanSpace ℝ (Fin D)) R
/-- Gelfand problem in the ball as a PDE: the closed ball of the problem (centre, radius). -/
def gelfandPdeClosedBall : Set (EuclideanSpace ℝ (Fin D)) := closedBall (C : EuclideanSpace ℝ (Fin D)) R
/-- Gelfand problem in the ball as a PDE: a classical solution is K times continuously differentiable on the open ball. -/
def gelfandPdeRegular (u : EuclideanSpace ℝ (Fin D) → ℝ) : Prop := ContDiffOn ℝ K u (ball C R)
/-- Gelfand problem in the ball as a PDE: a classical solution is continuous on the closed ball. -/
def gelfandPdeContinuous (u : EuclideanSpace ℝ (Fin D) → ℝ) : Prop := ContinuousOn u (closedBall C R)
/-- Gelfand problem in the ball as a PDE: λ is at most the reader's nine-decimal lower rounding of the critical parameter. -/
def gelfandPdeLamRange (lam : ℝ) : Prop := lam ≤ L
end Checked.Trust.SecondReading
```

No other definitions and no comments other than the module doc and the docstrings above (fill in the module doc's reader/sources/method). If the setting does not fit the template, do not change the shape: say so in the module doc and in your report.

Compile the file with `export PATH=$HOME/.elan/bin:$PATH; cd /home/claude/formalization; lake env lean runs/2026-11-07T0028Z/gelfand_pde_reader/SecondReadingGelfandPDE.lean` (timeout 300000 ms). A large Lean build is running on the machine; if the compile fails only for lack of memory, retry once after two minutes.

Finally report: the numerals D, C, R, K; your λ* with all digits you trust, the maximiser s, your error estimate and how you got it (two methods or tolerances); L; what you consulted; anything uncertain.
