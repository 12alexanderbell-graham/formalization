import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.ContinuousOn
/-! Blind literal reading of the Falkner–Skan problem (reader: Claude subagent, independent; derivation by hand from the stated eta and psi, giving f''' + f f'' + beta (1 - f'^2) = 0 with beta = 2m/(m+1), so beta = 1/2 at m = 1/3 and the coefficient of f f'' is 1 (the template shape fits); sigma and sigma0 computed by mpmath shooting (m = 1/3, bisection at 25 and 35 digits, lengths 10 and 14, plus scipy cross-check) and the m = 0 case by the scaling method at 30 and 40 digits; no outside sources; the error estimates decide all four roundings). -/
namespace Checked.Trust.SecondReading
open Set Filter Topology
/-- Falkner–Skan wedge flow with m = 1/3: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fskWedgeRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - 1 / 2 * (1 - p η ^ 2)
/-- Falkner–Skan problem: the closed half-line of η from the wall, with the type written out. -/
def fskHalfLineTyped : Set ℝ := Ici (0 : ℝ)
/-- Falkner–Skan problem: the closed half-line of η from the wall. -/
def fskHalfLine : Set ℝ := Ici 0
/-- Falkner–Skan problem: the wall condition on f and on f' (the value at the wall). -/
def fskWall (g : ℝ → ℝ) : Prop := g 0 = 0
/-- Falkner–Skan problem: the limit of f' at the edge of the layer, as a neighbourhood filter of that value. -/
noncomputable def fskEdge : Filter ℝ := 𝓝 1
/-- Falkner–Skan wedge flow with m = 1/3: the wall value of q = f'' lies strictly between the two nine-decimal roundings of σ. -/
def fskWedgeShear (q : ℝ → ℝ) : Prop := 0.927680039 < q 0 ∧ q 0 < 0.927680040
/-- Falkner–Skan flat plate (m = 0): the wall value of q = f'' lies between the two thirteen-decimal roundings of σ₀. -/
def fskPlateShear (q : ℝ → ℝ) : Prop := 0.4695999883610 ≤ q 0 ∧ q 0 ≤ 0.4695999883611
end Checked.Trust.SecondReading
