import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.ContinuousOn
/-! Blind literal reading of the Townes soliton problem (run 2026-11-07T0828Z): the right-hand side of the radial equation, the centre, the slope there, the limit at infinity, the radial intervals and half-lines, the two ten-decimal roundings of the ground state's central value and the event horizon. Copied verbatim (code) from `runs/2026-11-07T0828Z/townes_reader/SecondReadingTownes.lean`, written by a blind reader (Sonnet subagent) from the brief committed alone before it in that folder. Source: the reader's own derivation from the planar radial Laplacian and its own multiprecision shooting computation; nothing external consulted. -/
namespace Checked.Trust.SecondReading
open Set Filter Topology
/-- Townes radial problem: the right-hand side of φ' (where φ = θ') at a radius r > 0. -/
noncomputable def townesRhs (r : ℝ) (θ φ : ℝ → ℝ) : ℝ := -(1 / r * φ r) + θ r - θ r ^ 3
/-- Townes radial problem: the closed radial interval from the centre to S. -/
def townesDomain (S : ℝ) : Set ℝ := Icc 0 S
/-- Townes radial problem: the radial interval from the centre (excluded) to S. -/
def townesPunctured (S : ℝ) : Set ℝ := Ioc 0 S
/-- Townes radial problem: the closed half-line of radii from the centre. -/
def townesHalfLine : Set ℝ := Ici 0
/-- Townes radial problem: the open half-line of radii, centre excluded. -/
def townesOpenHalfLine : Set ℝ := Ioi 0
/-- Townes radial problem: regularity at the centre, φ continuous at the centre within the radial interval up to S. -/
def townesRegular (φ : ℝ → ℝ) (S : ℝ) : Prop := ContinuousWithinAt φ (Icc 0 S) 0
/-- Townes radial problem: regularity at the centre, φ continuous at the centre within the closed half-line. -/
def townesRegularHalfLine (φ : ℝ → ℝ) : Prop := ContinuousWithinAt φ (Ici 0) 0
/-- Townes radial problem: the condition on the slope φ = θ' at the centre. -/
def townesSlope (φ : ℝ → ℝ) : Prop := φ 0 = 0
/-- Townes radial problem: the central value of θ is c. -/
def townesCentre (θ : ℝ → ℝ) (c : ℝ) : Prop := θ 0 = c
/-- Townes radial problem: the limit of the profile at infinity, as a neighbourhood filter of that value. -/
noncomputable def townesInfinity : Filter ℝ := 𝓝 0
/-- Townes radial problem: shooting from the lower ten-decimal rounding of the ground state's central value. -/
def townesUnderStart (θ : ℝ → ℝ) : Prop := θ 0 = 2.2062008646
/-- Townes radial problem: shooting from the upper ten-decimal rounding of the ground state's central value. -/
def townesOverStart (θ : ℝ → ℝ) : Prop := θ 0 = 2.2062008647
/-- Townes radial problem: the open interval between the two roundings of the central value. -/
def townesBracket : Set ℝ := Ioo 2.2062008646 2.2062008647
/-- Townes radial problem: the radii from the centre (excluded) up to the event horizon H. -/
def townesHorizon : Set ℝ := Ioc 0 (68 / 5)
end Checked.Trust.SecondReading
