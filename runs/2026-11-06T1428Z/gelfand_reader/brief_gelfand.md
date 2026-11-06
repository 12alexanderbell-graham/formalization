# Brief: blind literal reading of the radial Gelfand problem in the three-dimensional ball (run 2026-11-06T1428Z)

You are an independent reader. Do not read anything in /home/claude/formalization except this brief and the output path below; in particular never open `Checked/`, `Work/`, `runs/` (other than this folder), `scripts/`, `validation/`, `.lake/` or any `*.md` there, and do not use git to look at history.

## The problem

The Gelfand (Liouville–Bratu–Gelfand, Frank-Kamenetskii) problem in the unit ball B of three-dimensional space: Δu + λ e^u = 0 in B, u = 0 on the boundary sphere, λ > 0. Radial solutions u(r), r = |x|, are regular at the centre. The standard reduction (Chandrasekhar's isothermal / Emden–Chandrasekhar form) rescales the radius and shifts u by its central value: s = r·√(λ·e^{u(0)}) and w(s) = u(r) − u(0). Derive yourself (from Δ in spherical coordinates for a radial function) the ODE that w satisfies in s, the initial conditions of w at the centre, and λ expressed through w and the scaled radius s of the boundary sphere (use u = 0 on the boundary). You may consult a textbook or the literature to confirm the reduction (for arXiv use only arxiv.org/abs or arxiv.org/pdf pages; never ar5iv, never e-print); a failed, blocked or timed-out WebFetch/WebSearch is recorded as "not read" — never fetch the same content with curl, wget or code. Downloaded files go to a temporary directory outside the repository (e.g. /tmp/gelfand_reader).

## What to write

ONE Lean 4 file `runs/2026-11-06T1428Z/gelfand_reader/SecondReadingGelfand.lean`, with exactly this template; replace each capital placeholder `A`, `B`, `C`, `D` by the numeral your derivation gives (integer numerals, written plainly, e.g. `7`; nothing else changes: keep every other token, the parentheses, the operators and their order exactly as shown):

```lean
import Mathlib.Analysis.SpecialFunctions.Exp
/-! Blind literal reading of the radial Gelfand problem in the three-dimensional ball (reader: <you>; derivation and sources: <what you used>). -/
namespace Checked.Trust.SecondReading
open Set
/-- Radial Gelfand problem in the 3-D ball, scaled form: the right-hand side of φ' where φ = w' (so w'' = this expression at s), at a scaled radius s > 0. -/
noncomputable def gelfandRhs (s : ℝ) (w φ : ℝ → ℝ) : ℝ := -(A / s * φ s) - Real.exp (w s)
/-- Radial Gelfand problem in the 3-D ball: the parameter λ of the solution whose boundary sphere sits at scaled radius s. -/
noncomputable def gelfandLambda (s : ℝ) (w : ℝ → ℝ) : ℝ := s ^ B * Real.exp (w s)
/-- Radial Gelfand problem in the 3-D ball: the initial condition on w at the centre (the centre's scaled radius, then the value of w there). -/
def gelfandCentre (w : ℝ → ℝ) : Prop := w C = D
/-- Radial Gelfand problem in the 3-D ball: regularity at the centre, φ = w' continuous at the centre within the radial interval up to S. -/
def gelfandRegular (φ : ℝ → ℝ) (S : ℝ) : Prop := ContinuousWithinAt φ (Icc C S) C
/-- Radial Gelfand problem in the 3-D ball: the closed radial interval from the centre to S. -/
def gelfandDomain (S : ℝ) : Set ℝ := Icc C S
/-- Radial Gelfand problem in the 3-D ball: the radial interval from the centre (excluded) to S, where the equation is singular-free. -/
def gelfandPunctured (S : ℝ) : Set ℝ := Ioc C S
end Checked.Trust.SecondReading
```

(`C` is the same numeral in every place it occurs.) No other definitions and no comments other than the module doc and the docstrings above (fill in the module doc's reader/sources). If your derivation does not fit the template (for example a sign or a factor that the shape cannot express), do not change the shape: say so in the module doc and in your report.

Compile the file with `export PATH=$HOME/.elan/bin:$PATH; cd /home/claude/formalization; lake env lean runs/2026-11-06T1428Z/gelfand_reader/SecondReadingGelfand.lean` (timeout 300000 ms). A large Lean build is running on the machine; if the compile fails only for lack of memory, retry once after two minutes.

Finally report: the four numerals, your derivation in a few lines (the ODE in s, the initial conditions, λ in terms of w at the boundary), what you consulted, and anything uncertain.
