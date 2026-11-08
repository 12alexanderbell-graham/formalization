# Brief: blind literal reading of the Homann stagnation-point problem (run 2026-11-08T0428Z)

You are an independent reader. Do not read anything in /home/claude/formalization except this brief and the output path below; in particular never open `Checked/`, `Work/`, `_archive/`, `runs/` (other than this folder), `scripts/`, `validation/`, `.lake/` or any `*.md` there, and do not use git to look at history.

## The problem

Steady axisymmetric stagnation-point flow of an incompressible fluid (kinematic viscosity ν) against a flat wall z = 0 (Homann flow). In cylindrical coordinates (r, z), far from the wall the flow is the inviscid axisymmetric stagnation-point flow u_r = a r, u_z = −2 a z (a > 0). Look for a similarity solution of the Navier–Stokes equations with the similarity variable η = z·√(a/ν) and the velocity field u_r = a r f'(η), u_z = −2 √(a ν) f(η) (this satisfies continuity). The problem reduces to a third-order ODE for f on η ≥ 0 with no-slip and no-penetration conditions at the wall and u → a x (the outer flow) at the edge of the layer. The wall shear is proportional to f''(wall).

You have four jobs.

1. **Derive the ODE and the boundary conditions in exactly this normalisation** (η and ψ as defined above; do not rescale). With p = f' and q = f'', write the ODE as q' = an expression in f, p, q and put it in the shape `-(K * f η * q η) - A + p η ^ B` (K, A and B plain integer numerals; signs are the operators shown). Give the value Z of η at the wall, the value Y of f and of f' at the wall, and the limit E of f'(η) as η → ∞ (plain integer numerals).

2. **Compute the wall value σ = f''(wall) yourself.** Do not look it up; compute it, e.g. by shooting with high precision (Python `mpmath`, at least 30 significant digits): integrate f(Z) = Y, f'(Z) = Y, f''(Z) = s and solve for s such that f' tends to E. Check it by a second, independent route (a second precision and a second method or integration length). Estimate your error. Let `L` be the largest number with exactly ten digits after the decimal point that does not exceed σ (round down), and `U` the smallest number with exactly ten digits after the decimal point that is not below σ (round up). If your error estimate does not decide the tenth digit, say so in the report and in the module doc.

3. **Shooting events.** Integrate the initial-value problem twice more, once with f''(Z) = L and once with f''(Z) = U (your L and U from job 2). For the start value L, find R_L = the first η > Z at which q = f'' becomes negative (the profile turns back before reaching the outer velocity); for the start value U, find R_U = the first η > Z at which f' exceeds E (the profile overshoots the outer velocity). (If an event does not happen, or the other event happens first, say so.) Let R = max(R_L, R_U). Then let H be the smallest integer with H ≥ R + 1/2 (round up to an integer, after adding a margin of one half).

4. **Fill in the template below.**

Scripts and scratch files go to a temporary directory outside the repository (e.g. /tmp/homann_reader). Web access: a failed, blocked or timed-out WebFetch/WebSearch is recorded as "not read" — never fetch the same content with curl, wget or code; for arXiv only arxiv.org/abs or arxiv.org/pdf, never ar5iv or e-print. Do not take σ or the event radii from any web page or book: the point is an independent computation.

## What to write

ONE Lean 4 file `runs/2026-11-08T0428Z/homann_reader/SecondReadingHomann.lean`, with exactly the template below. Replace each capital placeholder by your numeral: `K`, `A`, `B`, `Z`, `Y`, `E`, `H` plain integer numerals from jobs 1 and 3 (`Z` stands in several places, always the same numeral); `L` and `U` your ten-decimal numbers written as plain decimals (digits, one point, ten digits). Nothing else changes: keep every other token, the parentheses and the order exactly as shown (the capital `S` in `homannWindowTyped (S : ℝ)` and `homannWindow (S : ℝ)` is a variable, not a placeholder: keep it).

```lean
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.ContinuousOn
/-! Blind literal reading of the Homann stagnation-point problem (reader: <you>; derivation, computation and sources: <what you used>). -/
namespace Checked.Trust.SecondReading
open Set Filter Topology
/-- Homann problem: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def homannRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(K * f η * q η) - A + p η ^ B
/-- Homann problem: the closed half-line of η from the wall, with the type written out. -/
def homannHalfLineTyped : Set ℝ := Ici (Z : ℝ)
/-- Homann problem: the closed half-line of η from the wall. -/
def homannHalfLine : Set ℝ := Ici Z
/-- Homann problem: the closed interval of η from the wall to S, with the type written out. -/
def homannWindowTyped (S : ℝ) : Set ℝ := Icc (Z : ℝ) S
/-- Homann problem: the closed interval of η from the wall to S. -/
def homannWindow (S : ℝ) : Set ℝ := Icc Z S
/-- Homann problem: the wall condition on f and on f' (the value at the wall). -/
def homannWall (g : ℝ → ℝ) : Prop := g Z = Y
/-- Homann problem: the limit of f' at the edge of the layer, as a neighbourhood filter of that value. -/
noncomputable def homannEdge : Filter ℝ := 𝓝 E
/-- Homann problem: shooting from below, the wall value of q = f'' set to the ten-decimal rounding of σ downwards. -/
def homannStartLow (q : ℝ → ℝ) : Prop := q Z = L
/-- Homann problem: shooting from above, the wall value of q = f'' set to the ten-decimal rounding of σ upwards. -/
def homannStartHigh (q : ℝ → ℝ) : Prop := q Z = U
/-- Homann problem: the wall value of q = f'' lies strictly between the two ten-decimal roundings of σ. -/
def homannShear (q : ℝ → ℝ) : Prop := L < q Z ∧ q Z < U
/-- Homann problem: the interval of η, after the wall, within which both shooting events happen. -/
def homannHorizon : Set ℝ := Ioc (Z : ℝ) H
end Checked.Trust.SecondReading
```

No other definitions and no comments other than the module doc and the docstrings above (fill in the module doc's reader/sources/method). If the problem does not fit the template, do not change the shape: say so in the module doc and in your report.

Compile the file with `export PATH=$HOME/.elan/bin:$PATH; cd /home/claude/formalization; lake env lean runs/2026-11-08T0428Z/homann_reader/SecondReadingHomann.lean` (timeout 300000 ms). Do not run `lake build`.

Finally report: K, A, B, Z, Y, E; your σ with all digits you trust, your error estimate and how you got it (two methods or precisions); L and U; R_L, R_U and H; what you consulted; anything uncertain.
