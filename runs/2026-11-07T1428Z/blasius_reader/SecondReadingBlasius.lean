import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.ContinuousOn
/-! Blind literal reading of the Blasius boundary-layer problem (reader: blind independent reader; derivation, computation and sources: own derivation f''' + f f''/2 = 0 from psi = sqrt(nu U x) f(eta); sigma = 0.332057336215196298937180062... computed by mpmath Taylor shooting, once via the scaling f(eta) = lambda F(lambda eta), once by direct shooting with findroot at length 22; the two agree to about 30 digits, so the fourteenth digit is decided; no web or book sources consulted). -/
namespace Checked.Trust.SecondReading
open Set Filter Topology
/-- Blasius problem: the right-hand side of q' (where q = f'') at η. -/
noncomputable def blasiusRhs (f q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η / 2)
/-- Blasius problem: the closed half-line of η from the wall, with the type written out. -/
def blasiusHalfLineTyped : Set ℝ := Ici (0 : ℝ)
/-- Blasius problem: the closed half-line of η from the wall. -/
def blasiusHalfLine : Set ℝ := Ici 0
/-- Blasius problem: the wall condition on f and on f' (the value at the wall). -/
def blasiusWall (g : ℝ → ℝ) : Prop := g 0 = 0
/-- Blasius problem: the limit of f' at the edge of the layer, as a neighbourhood filter of that value. -/
noncomputable def blasiusEdge : Filter ℝ := 𝓝 1
/-- Blasius problem: the wall value of q = f'' lies between the two fourteen-decimal roundings of σ. -/
def blasiusShear (q : ℝ → ℝ) : Prop := 0.33205733621519 ≤ q 0 ∧ q 0 ≤ 0.33205733621520
end Checked.Trust.SecondReading
