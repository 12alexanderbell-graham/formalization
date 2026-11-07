import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.ContinuousOn
/-! Blind literal reading of the Blasius boundary-layer problem (run 2026-11-07T1428Z): the coefficient of the third-order equation in the similarity normalisation, the wall, the wall values, the edge limit, the half-lines and the two fourteen-decimal roundings of the wall value of f''. Copied verbatim (code) from `runs/2026-11-07T1428Z/blasius_reader/SecondReadingBlasius.lean`, written by a blind reader (Sonnet subagent) from the brief committed alone before it in that folder. Source: the reader's own derivation from the similarity variables and its own multiprecision computation by two routes; nothing external consulted. -/
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
