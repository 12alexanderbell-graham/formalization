# Brief: blind literal reading of the Townes soliton problem (run 2026-11-07T0828Z)

You are an independent reader. Do not read anything in /home/claude/formalization except this brief and the output path below; in particular never open `Checked/`, `Work/`, `_archive/`, `runs/` (other than this folder), `scripts/`, `validation/`, `.lake/` or any `*.md` there, and do not use git to look at history.

## The problem

The Townes soliton is the ground state of the two-dimensional cubic focusing nonlinear Schrödinger equation: the positive, radially symmetric solution Q of ΔQ − Q + Q³ = 0 in the plane ℝ² that decays to zero at infinity. Write Q(x) = θ(|x|) with r = |x| ≥ 0 and φ = θ' (the radial derivative). The radial profile solves a second-order ODE in r with a singular point at the centre r = 0; regularity of Q at the origin fixes the slope there, and the central value θ(centre) is the shooting parameter that selects the ground state.

You have three jobs.

1. **Derive the radial problem.** From the planar Laplacian of a radial function, write φ' = θ'' as an expression in r, θ(r), φ(r), in exactly the shape `-(A / r * φ r) + θ r - θ r ^ C` (find A and C); give the radius of the centre, the slope of a regular radial solution at the centre, and the limit of θ at infinity.

2. **Compute the central value Q(0) of the ground state yourself.** Do not look it up; compute it by shooting: start at the singular point with a power series in r (only even powers), integrate with high precision (for example Python `mpmath` with at least 30 significant digits and an independent check: a second tolerance or a second method), and bisect on θ(centre) between "undershoot" (φ becomes positive while θ is still positive) and "overshoot" (θ becomes negative while φ is still negative). Estimate your error. Then let `L` be the largest number with exactly ten digits after the decimal point that does not exceed your Q(0) (round down), and `U` the smallest number with exactly ten digits after the decimal point that is not below it (round up). If your error estimate does not decide the tenth digit, say so in the report and in the module doc.

3. **Event radii.** Integrate once from θ(centre) = L and once from θ(centre) = U (same method). Record r_L, the first radius at which φ becomes positive in the run from L (θ positive until then), and r_U, the first radius at which θ becomes negative in the run from U (φ negative until then). If a run does not show the expected event, say so. Let `H` be the smallest multiple of 1/5 that is at least max(r_L, r_U); write it as a fraction `p / q` in lowest terms.

Scripts and scratch files go to a temporary directory outside the repository (e.g. /tmp/townes_reader). Web access: a failed, blocked or timed-out WebFetch/WebSearch is recorded as "not read" — never fetch the same content with curl, wget or code; for arXiv only arxiv.org/abs or arxiv.org/pdf, never ar5iv or e-print. Do not take Q(0) or the event radii from any web page or book: the point is an independent computation.

## What to write

ONE Lean 4 file `runs/2026-11-07T0828Z/townes_reader/SecondReadingTownes.lean`, with exactly the template below. Replace each capital placeholder by your numeral: `A` and `C` plain integer numerals from job 1; `Z` the radius of the centre, `W` the slope at the centre, `Y` the limit at infinity (plain integer numerals; `Z` stands in several places, always the same numeral); `L` and `U` your ten-decimal numbers written as plain decimals (digits, one point, ten digits); `H` your fraction written as `p / q` (the parentheses around it stay). Nothing else changes: keep every other token, the parentheses and the order exactly as shown.

```lean
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.ContinuousOn
/-! Blind literal reading of the Townes soliton problem (reader: <you>; derivation, computation and sources: <what you used>). -/
namespace Checked.Trust.SecondReading
open Set Filter Topology
/-- Townes radial problem: the right-hand side of φ' (where φ = θ') at a radius r > 0. -/
noncomputable def townesRhs (r : ℝ) (θ φ : ℝ → ℝ) : ℝ := -(A / r * φ r) + θ r - θ r ^ C
/-- Townes radial problem: the closed radial interval from the centre to S. -/
def townesDomain (S : ℝ) : Set ℝ := Icc Z S
/-- Townes radial problem: the radial interval from the centre (excluded) to S. -/
def townesPunctured (S : ℝ) : Set ℝ := Ioc Z S
/-- Townes radial problem: the closed half-line of radii from the centre. -/
def townesHalfLine : Set ℝ := Ici Z
/-- Townes radial problem: the open half-line of radii, centre excluded. -/
def townesOpenHalfLine : Set ℝ := Ioi Z
/-- Townes radial problem: regularity at the centre, φ continuous at the centre within the radial interval up to S. -/
def townesRegular (φ : ℝ → ℝ) (S : ℝ) : Prop := ContinuousWithinAt φ (Icc Z S) Z
/-- Townes radial problem: regularity at the centre, φ continuous at the centre within the closed half-line. -/
def townesRegularHalfLine (φ : ℝ → ℝ) : Prop := ContinuousWithinAt φ (Ici Z) Z
/-- Townes radial problem: the condition on the slope φ = θ' at the centre. -/
def townesSlope (φ : ℝ → ℝ) : Prop := φ Z = W
/-- Townes radial problem: the central value of θ is c. -/
def townesCentre (θ : ℝ → ℝ) (c : ℝ) : Prop := θ Z = c
/-- Townes radial problem: the limit of the profile at infinity, as a neighbourhood filter of that value. -/
noncomputable def townesInfinity : Filter ℝ := 𝓝 Y
/-- Townes radial problem: shooting from the lower ten-decimal rounding of the ground state's central value. -/
def townesUnderStart (θ : ℝ → ℝ) : Prop := θ Z = L
/-- Townes radial problem: shooting from the upper ten-decimal rounding of the ground state's central value. -/
def townesOverStart (θ : ℝ → ℝ) : Prop := θ Z = U
/-- Townes radial problem: the open interval between the two roundings of the central value. -/
def townesBracket : Set ℝ := Ioo L U
/-- Townes radial problem: the radii from the centre (excluded) up to the event horizon H. -/
def townesHorizon : Set ℝ := Ioc Z (H)
end Checked.Trust.SecondReading
```

No other definitions and no comments other than the module doc and the docstrings above (fill in the module doc's reader/sources/method). If the problem does not fit the template, do not change the shape: say so in the module doc and in your report.

Compile the file with `export PATH=$HOME/.elan/bin:$PATH; cd /home/claude/formalization; lake env lean runs/2026-11-07T0828Z/townes_reader/SecondReadingTownes.lean` (timeout 300000 ms).

Finally report: A, C, Z, W, Y; your Q(0) with all digits you trust and your error estimate and how you got it (two methods or tolerances); L and U; r_L, r_U and H; what you consulted; anything uncertain.
