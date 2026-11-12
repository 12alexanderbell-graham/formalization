import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Interval.Set.Basic
/-! Blind literal reading of the Bonnor–Ebert sphere (run 2026-11-12T0628Z): the dimensionless pressure-confined mass, the centre-to-edge density contrast, and the right end and the radial range of the interval on which the claim states that the mass decreases. Copied verbatim (code) from `runs/2026-11-12T0628Z/be_reader/SecondReadingBE.lean`, written by a blind reader (Sonnet subagent) from the brief committed alone before it in that folder. Source: the reader's own derivation from the isothermal sphere in hydrostatic equilibrium and the definition of the dimensionless mass, and the claim's own words; nothing external consulted. -/
namespace Checked.Trust.SecondReading
open Set
/-- Bonnor–Ebert sphere: the dimensionless mass m(s) = M G^{3/2} P_ext^{1/2} / c_s⁴ of the sphere truncated at dimensionless radius s, in terms of w = −ψ and φ = w'. -/
noncomputable def beMass (s : ℝ) (w φ : ℝ → ℝ) : ℝ := s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)
/-- Bonnor–Ebert sphere: the centre-to-edge density contrast ρ_c / ρ(s) of the sphere truncated at dimensionless radius s, in terms of w = −ψ. -/
noncomputable def beContrast (s : ℝ) (w : ℝ → ℝ) : ℝ := Real.exp ((-1) * w s)
/-- Bonnor–Ebert sphere: the right end of the radial interval on which the claim below states that the mass decreases. -/
def beDecreaseEnd : ℝ := 7
/-- Bonnor–Ebert sphere: the closed radial range, from the radius ξ of the maximum to the end stated in the claim, on which the mass decreases. -/
def beDecreaseRange (ξ : ℝ) : Set ℝ := Icc ξ 7
end Checked.Trust.SecondReading
