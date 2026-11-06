# Brief: blind literal reading of the Thomas–Fermi problem of the neutral atom (run 2026-11-06T2028Z)

You are an independent reader. Do not read anything in /home/claude/formalization except this brief and the output path below; in particular never open `Checked/`, `Work/`, `runs/` (other than this folder), `scripts/`, `validation/`, `.lake/` or any `*.md` there, and do not use git to look at history.

## The problem

The dimensionless Thomas–Fermi equation of the neutral atom (Thomas 1927, Fermi 1927; the screening function φ_TF(x) of the Thomas–Fermi atom, x the scaled distance from the nucleus): a second-order ODE for y(x) on x > 0 with a boundary condition at the nucleus and one at infinity (the neutral atom). From your own knowledge of the Thomas–Fermi model (and a textbook or the literature if you wish) determine: the exponent of y and the power of x in the equation y'' = (power of y)/(power of x); the point of the half-line where the nucleus sits and the value of y there; the value y tends to at infinity for the neutral atom. For arXiv use only arxiv.org/abs or arxiv.org/pdf pages; never ar5iv, never e-print. A failed, blocked or timed-out WebFetch/WebSearch is recorded as "not read" — never fetch the same content with curl, wget or code. Downloaded files go to a temporary directory outside the repository (e.g. /tmp/tf_reader).

## What to write

ONE Lean 4 file `runs/2026-11-06T2028Z/tf_reader/SecondReadingTF.lean`, with exactly this template; replace each capital placeholder `A`, `B`, `C`, `D`, `E` by the numeral your reading gives (integer numerals, written plainly, e.g. `7`; nothing else changes: keep every other token, the parentheses, the operators and their order exactly as shown). The exponent of y is written as the fraction A / B in lowest terms; the power of x in the denominator is expressed through `Real.sqrt` (if your reading of the power of x is not one half, say so in the module doc and in your report, and keep the template).

```lean
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Filter.Basic
/-! Blind literal reading of the Thomas–Fermi problem of the neutral atom (reader: <you>; sources: <what you used>). -/
namespace Checked.Trust.SecondReading
open Set Filter Topology
/-- Thomas–Fermi equation of the neutral atom: the right-hand side of y'' at a scaled distance x > 0. -/
noncomputable def tfRhs (y : ℝ → ℝ) (x : ℝ) : ℝ := y x ^ ((A : ℝ) / B) / Real.sqrt x
/-- Thomas–Fermi problem: the closed half-line of scaled distances, starting at the nucleus. -/
def tfDomain : Set ℝ := Ici C
/-- Thomas–Fermi problem: the boundary condition at the nucleus (its scaled distance, then the value of y there). -/
def tfNucleus (y : ℝ → ℝ) : Prop := y C = D
/-- Thomas–Fermi problem of the neutral atom: the limit of y at infinity, as a neighbourhood filter of that value. -/
noncomputable def tfInfinity : Filter ℝ := 𝓝 E
/-- Thomas–Fermi problem: a function evaluated at the nucleus (used for the initial slope y'(nucleus)). -/
def tfAtNucleus (φ : ℝ → ℝ) : ℝ := φ C
end Checked.Trust.SecondReading
```

(`C` is the same numeral in every place it occurs.) No other definitions and no comments other than the module doc and the docstrings above (fill in the module doc's reader/sources). If your reading does not fit the template, do not change the shape: say so in the module doc and in your report.

Compile the file with `export PATH=$HOME/.elan/bin:$PATH; cd /home/claude/formalization; lake env lean runs/2026-11-06T2028Z/tf_reader/SecondReadingTF.lean` (timeout 300000 ms). A Lean build is running on the machine; if the compile fails only for lack of memory, retry once after two minutes.

Finally report: the five numerals, the equation and boundary conditions as you read them, what you consulted, and anything uncertain.
