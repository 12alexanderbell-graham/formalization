import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.ContinuousOn
/-! Blind literal reading of the Hiemenz stagnation-point problem (reader: independent blind reader; derivation, computation and sources: own derivation f''' + f f'' + 1 - f'^2 = 0 with f(0)=f'(0)=0, f'(∞)=1; sigma = f''(0) = 1.23258765682028102017394 computed by mpmath shooting (dps 35 and 45, lengths 10 and 12) and checked with scipy solve_bvp; error below 1e-20, so the tenth digit is decided; no external sources). -/
namespace Checked.Trust.SecondReading
open Set Filter Topology
/-- Hiemenz problem: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def hiemenzRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - 1 + p η ^ 2
/-- Hiemenz problem: the closed half-line of η from the wall, with the type written out. -/
def hiemenzHalfLineTyped : Set ℝ := Ici (0 : ℝ)
/-- Hiemenz problem: the closed half-line of η from the wall. -/
def hiemenzHalfLine : Set ℝ := Ici 0
/-- Hiemenz problem: the closed interval of η from the wall to S, with the type written out. -/
def hiemenzWindowTyped (S : ℝ) : Set ℝ := Icc (0 : ℝ) S
/-- Hiemenz problem: the closed interval of η from the wall to S. -/
def hiemenzWindow (S : ℝ) : Set ℝ := Icc 0 S
/-- Hiemenz problem: the wall condition on f and on f' (the value at the wall). -/
def hiemenzWall (g : ℝ → ℝ) : Prop := g 0 = 0
/-- Hiemenz problem: the limit of f' at the edge of the layer, as a neighbourhood filter of that value. -/
noncomputable def hiemenzEdge : Filter ℝ := 𝓝 1
/-- Hiemenz problem: shooting from below, the wall value of q = f'' set to the ten-decimal rounding of σ downwards. -/
def hiemenzStartLow (q : ℝ → ℝ) : Prop := q 0 = 1.2325876568
/-- Hiemenz problem: shooting from above, the wall value of q = f'' set to the ten-decimal rounding of σ upwards. -/
def hiemenzStartHigh (q : ℝ → ℝ) : Prop := q 0 = 1.2325876569
/-- Hiemenz problem: the wall value of q = f'' lies strictly between the two ten-decimal roundings of σ. -/
def hiemenzShear (q : ℝ → ℝ) : Prop := 1.2325876568 < q 0 ∧ q 0 < 1.2325876569
/-- Hiemenz problem: the interval of η, after the wall, within which both shooting events happen. -/
def hiemenzHorizon : Set ℝ := Ioc (0 : ℝ) (15 / 2)
end Checked.Trust.SecondReading
