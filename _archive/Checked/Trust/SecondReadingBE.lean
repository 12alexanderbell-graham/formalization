import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
/-! Blind literal reading of the Bonnor–Ebert mass, density contrast and decrease horizon (run 2026-11-12T0427Z). Copied verbatim (code) from `runs/2026-11-12T0427Z/be_reader/SecondReadingBE.lean`, written by a blind reader (Sonnet subagent) from the brief committed alone before it in that folder. Source: the reader's own derivation from the mass of an isothermal sphere and the confining pressure at its edge, and the claim's own words for the horizon. -/
namespace Checked.Trust.SecondReading
/-- Bonnor–Ebert sphere: the dimensionless mass m(s) = M G^{3/2} P_ext^{1/2} / c_s⁴ of the sphere truncated at dimensionless radius s, in terms of w = −ψ and φ = w'. -/
noncomputable def beMass (s : ℝ) (w φ : ℝ → ℝ) : ℝ := s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)
/-- Bonnor–Ebert sphere: the centre-to-edge density contrast ρ_c / ρ(s) of the sphere truncated at dimensionless radius s, in terms of w = −ψ. -/
noncomputable def beContrast (s : ℝ) (w : ℝ → ℝ) : ℝ := Real.exp ((-1) * w s)
/-- Bonnor–Ebert sphere: the right end of the radial interval on which the claim below states that the mass decreases. -/
def beDecreaseEnd : ℝ := 7
end Checked.Trust.SecondReading
