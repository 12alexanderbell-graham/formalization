# Brief: blind literal reading of two Falkner–Skan problems (run 2026-11-08T0828Z)

You are an independent reader. Do not read anything in /home/claude/formalization except this brief and the output path below; in particular never open `Checked/`, `Work/`, `_archive/`, `runs/` (other than this folder), `scripts/`, `validation/`, `.lake/` or any `*.md` there, and do not use git to look at history.

## The problem

Steady two-dimensional boundary layer of an incompressible fluid (kinematic viscosity ν) on a wall y = 0, x > 0, under an outer (inviscid) stream U(x) = a·x^m (a > 0). This is the Falkner–Skan family (flow past a wedge). Look for a similarity solution of the boundary-layer equations with

* similarity variable η = y·√((m + 1)·U(x) / (2 ν x)),
* stream function ψ = √(2 ν x U(x) / (m + 1)) · f(η), so u = ∂ψ/∂y and v = −∂ψ/∂x,

with no slip and no penetration at the wall and u → U(x) at the edge of the layer. The problem reduces to a third-order ODE for f on η ≥ 0. Two cases are wanted: the wedge with **m = 1/3**, and the flat plate **m = 0**.

You have four jobs.

1. **Derive the ODE and the boundary conditions in exactly this normalisation** (η and ψ as defined above; do not rescale), for general m and then for m = 1/3. With p = f' and q = f'', write the ODE as q' = an expression in f, p, q. In the template below it must have the shape `-(f η * q η) - BETA * (A - p η ^ C)`: BETA is the coefficient that depends on m, evaluated at m = 1/3 and written as an exact fraction `n / d` (two integer numerals with ` / ` between them; if it is an integer write it as an integer); A and C are plain integer numerals. If your derived equation does not have this shape (for instance the coefficient of f f'' is not 1 in this normalisation), say so in the module doc and in the report and do not force it. Give the value Z of η at the wall, the value Y of f and of f' at the wall, and the limit E of f'(η) as η → ∞ (plain integer numerals). Check that for m = 0 your equation has no term without f'' (it should reduce to the flat-plate equation in this normalisation).

2. **Compute σ = f''(wall) for m = 1/3 yourself.** Do not look it up; compute it, e.g. by shooting with high precision (Python `mpmath`, at least 30 significant digits): integrate f(Z) = Y, f'(Z) = Y, f''(Z) = s and solve for s such that f' tends to E. Check it by a second, independent route (a second precision and a second method or integration length). Estimate your error. Let `L` be the largest number with exactly **nine** digits after the decimal point that does not exceed σ (round down), and `U` the smallest number with exactly nine digits after the decimal point that is not below σ (round up). Write both with all nine digits after the point (keep trailing zeros).

3. **Compute σ₀ = f''(wall) for m = 0 yourself** in the same way (two routes, error estimate). Let `L0` be σ₀ rounded down and `U0` σ₀ rounded up, each with exactly **thirteen** digits after the decimal point (keep trailing zeros). If your error estimate does not decide a rounding (job 2 or 3), say so in the report and in the module doc.

4. **Fill in the template below.**

Scripts and scratch files go to a temporary directory outside the repository (e.g. /tmp/fs_reader). Web access: a failed, blocked or timed-out WebFetch/WebSearch is recorded as "not read" — never fetch the same content with curl, wget or code; for arXiv only arxiv.org/abs or arxiv.org/pdf, never ar5iv or e-print. Do not take σ or σ₀ from any web page or book: the point is an independent computation.

## What to write

ONE Lean 4 file `runs/2026-11-08T0828Z/fs_reader/SecondReadingFalknerSkan.lean`, with exactly the template below. Replace each capital placeholder by your numeral: `A`, `C`, `Z`, `Y`, `E` plain integer numerals from job 1 (`Z` stands in several places, always the same numeral); `BETA` your exact fraction from job 1; `L`, `U` your nine-decimal numbers and `L0`, `U0` your thirteen-decimal numbers, written as plain decimals (digits, one point, the digits after it). Nothing else changes: keep every other token, the parentheses and the order exactly as shown.

```lean
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.ContinuousOn
/-! Blind literal reading of the Falkner–Skan problem (reader: <you>; derivation, computation and sources: <what you used>). -/
namespace Checked.Trust.SecondReading
open Set Filter Topology
/-- Falkner–Skan wedge flow with m = 1/3: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fskWedgeRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - BETA * (A - p η ^ C)
/-- Falkner–Skan problem: the closed half-line of η from the wall, with the type written out. -/
def fskHalfLineTyped : Set ℝ := Ici (Z : ℝ)
/-- Falkner–Skan problem: the closed half-line of η from the wall. -/
def fskHalfLine : Set ℝ := Ici Z
/-- Falkner–Skan problem: the wall condition on f and on f' (the value at the wall). -/
def fskWall (g : ℝ → ℝ) : Prop := g Z = Y
/-- Falkner–Skan problem: the limit of f' at the edge of the layer, as a neighbourhood filter of that value. -/
noncomputable def fskEdge : Filter ℝ := 𝓝 E
/-- Falkner–Skan wedge flow with m = 1/3: the wall value of q = f'' lies strictly between the two nine-decimal roundings of σ. -/
def fskWedgeShear (q : ℝ → ℝ) : Prop := L < q Z ∧ q Z < U
/-- Falkner–Skan flat plate (m = 0): the wall value of q = f'' lies between the two thirteen-decimal roundings of σ₀. -/
def fskPlateShear (q : ℝ → ℝ) : Prop := L0 ≤ q Z ∧ q Z ≤ U0
end Checked.Trust.SecondReading
```

No other definitions and no comments other than the module doc and the docstrings above (fill in the module doc's reader/sources/method). If the problem does not fit the template, do not change the shape: say so in the module doc and in your report.

Compile the file with `export PATH=$HOME/.elan/bin:$PATH; cd /home/claude/formalization; lake env lean runs/2026-11-08T0828Z/fs_reader/SecondReadingFalknerSkan.lean` (timeout 300000 ms). Do not run `lake build`. Another build may be running on the machine; that is expected, do not stop it.

Finally report: your general-m equation, BETA, A, C, Z, Y, E; σ and σ₀ with all digits you trust, your error estimates and how you got them (two methods or precisions); L, U, L0, U0; what you consulted; anything uncertain.
