# Brief: blind literal reading of the Blasius boundary-layer problem (run 2026-11-07T1428Z)

You are an independent reader. Do not read anything in /home/claude/formalization except this brief and the output path below; in particular never open `Checked/`, `Work/`, `_archive/`, `runs/` (other than this folder), `scripts/`, `validation/`, `.lake/` or any `*.md` there, and do not use git to look at history.

## The problem

Steady two-dimensional laminar flow of an incompressible fluid (kinematic viscosity ν) past a semi-infinite flat plate along y = 0, x > 0, with uniform free stream U∞ parallel to the plate. Prandtl's boundary-layer equations admit Blasius's similarity solution: with the similarity variable η = y·√(U∞ / (ν x)) and the stream function ψ = √(ν U∞ x) · f(η) (so that the streamwise velocity is u = U∞ f'(η)), the problem reduces to a third-order ODE for f on η ≥ 0 with no-slip and no-penetration conditions at the wall and u → U∞ at the edge of the layer. The wall shear is proportional to f''(wall).

You have three jobs.

1. **Derive the ODE and the boundary conditions in exactly this normalisation** (η and ψ as defined above; do not rescale). Write the ODE as f''' = an expression; with p = f' and q = f'', put it in the shape `q' = -(f η * q η / K)` and find K (a plain integer numeral). Give the value Z of η at the wall, the value Y of f and of f' at the wall, and the limit E of f'(η) as η → ∞ (plain integer numerals).

2. **Compute the wall value σ = f''(wall) yourself.** Do not look it up; compute it, for example by shooting: integrate the initial-value problem f(Z) = Y, f'(Z) = Y, f''(Z) = s with high precision (e.g. Python `mpmath` with at least 30 significant digits) and solve for s such that f'(∞) equals E, or use a scaling symmetry of the ODE if you find one. Check it by a second, independent route (a second precision/tolerance and a second method or a second integration length). Estimate your error. Then let `L` be the largest number with exactly fourteen digits after the decimal point that does not exceed your σ (round down), and `U` the smallest number with exactly fourteen digits after the decimal point that is not below it (round up). If your error estimate does not decide the fourteenth digit, say so in the report and in the module doc.

3. **Fill in the template below.**

Scripts and scratch files go to a temporary directory outside the repository (e.g. /tmp/blasius_reader). Web access: a failed, blocked or timed-out WebFetch/WebSearch is recorded as "not read" — never fetch the same content with curl, wget or code; for arXiv only arxiv.org/abs or arxiv.org/pdf, never ar5iv or e-print. Do not take σ from any web page or book: the point is an independent computation.

## What to write

ONE Lean 4 file `runs/2026-11-07T1428Z/blasius_reader/SecondReadingBlasius.lean`, with exactly the template below. Replace each capital placeholder by your numeral: `K`, `Z`, `Y`, `E` plain integer numerals from job 1 (`Z` stands in several places, always the same numeral); `L` and `U` your fourteen-decimal numbers written as plain decimals (digits, one point, fourteen digits). Nothing else changes: keep every other token, the parentheses and the order exactly as shown.

```lean
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.ContinuousOn
/-! Blind literal reading of the Blasius boundary-layer problem (reader: <you>; derivation, computation and sources: <what you used>). -/
namespace Checked.Trust.SecondReading
open Set Filter Topology
/-- Blasius problem: the right-hand side of q' (where q = f'') at η. -/
noncomputable def blasiusRhs (f q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η / K)
/-- Blasius problem: the closed half-line of η from the wall, with the type written out. -/
def blasiusHalfLineTyped : Set ℝ := Ici (Z : ℝ)
/-- Blasius problem: the closed half-line of η from the wall. -/
def blasiusHalfLine : Set ℝ := Ici Z
/-- Blasius problem: the wall condition on f and on f' (the value at the wall). -/
def blasiusWall (g : ℝ → ℝ) : Prop := g Z = Y
/-- Blasius problem: the limit of f' at the edge of the layer, as a neighbourhood filter of that value. -/
noncomputable def blasiusEdge : Filter ℝ := 𝓝 E
/-- Blasius problem: the wall value of q = f'' lies between the two fourteen-decimal roundings of σ. -/
def blasiusShear (q : ℝ → ℝ) : Prop := L ≤ q Z ∧ q Z ≤ U
end Checked.Trust.SecondReading
```

No other definitions and no comments other than the module doc and the docstrings above (fill in the module doc's reader/sources/method). If the problem does not fit the template, do not change the shape: say so in the module doc and in your report.

Compile the file with `export PATH=$HOME/.elan/bin:$PATH; cd /home/claude/formalization; lake env lean runs/2026-11-07T1428Z/blasius_reader/SecondReadingBlasius.lean` (timeout 300000 ms).

Finally report: K, Z, Y, E; your σ with all digits you trust, your error estimate and how you got it (two methods or precisions); L and U; what you consulted; anything uncertain.
