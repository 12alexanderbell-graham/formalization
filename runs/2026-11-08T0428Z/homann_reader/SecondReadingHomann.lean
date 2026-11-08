import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.ContinuousOn
/-! Blind literal reading of the Homann stagnation-point problem (reader: independent blind reader; derivation by hand from the Navier-Stokes equations, f''' = f'^2 - 1 - 2 f f'' with f(0)=f'(0)=0, f'(infinity)=1; sigma = 1.3119376938798051354816... computed by mpmath shooting at 30 and 40 digits with integration lengths 12 and 16, event radii by mpmath and scipy DOP853; no web or book sources; the error estimate decides the tenth digit). -/
namespace Checked.Trust.SecondReading
open Set Filter Topology
/-- Homann problem: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def homannRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(2 * f η * q η) - 1 + p η ^ 2
/-- Homann problem: the closed half-line of η from the wall, with the type written out. -/
def homannHalfLineTyped : Set ℝ := Ici (0 : ℝ)
/-- Homann problem: the closed half-line of η from the wall. -/
def homannHalfLine : Set ℝ := Ici 0
/-- Homann problem: the closed interval of η from the wall to S, with the type written out. -/
def homannWindowTyped (S : ℝ) : Set ℝ := Icc (0 : ℝ) S
/-- Homann problem: the closed interval of η from the wall to S. -/
def homannWindow (S : ℝ) : Set ℝ := Icc 0 S
/-- Homann problem: the wall condition on f and on f' (the value at the wall). -/
def homannWall (g : ℝ → ℝ) : Prop := g 0 = 0
/-- Homann problem: the limit of f' at the edge of the layer, as a neighbourhood filter of that value. -/
noncomputable def homannEdge : Filter ℝ := 𝓝 1
/-- Homann problem: shooting from below, the wall value of q = f'' set to the ten-decimal rounding of σ downwards. -/
def homannStartLow (q : ℝ → ℝ) : Prop := q 0 = 1.3119376938
/-- Homann problem: shooting from above, the wall value of q = f'' set to the ten-decimal rounding of σ upwards. -/
def homannStartHigh (q : ℝ → ℝ) : Prop := q 0 = 1.3119376939
/-- Homann problem: the wall value of q = f'' lies strictly between the two ten-decimal roundings of σ. -/
def homannShear (q : ℝ → ℝ) : Prop := 1.3119376938 < q 0 ∧ q 0 < 1.3119376939
/-- Homann problem: the interval of η, after the wall, within which both shooting events happen. -/
def homannHorizon : Set ℝ := Ioc (0 : ℝ) 6
end Checked.Trust.SecondReading
