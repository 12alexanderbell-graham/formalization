import Mathlib.Data.Real.Basic
/-! Blind literal reading of three κ(ω) correlations (reader: Claude subagent, sources: Reaktoro CubicEOS EquationModel API page (typeset LaTeX source of the docs); Cantera PengRobinson.h doxygen page; IDAES cubic EoS docs). The Cantera page prints 1.487503 and 0.016667 in the PR78 heavy branch, disagreeing with Reaktoro's 1.48503 and 0.016666; the latter (matching the original Robinson–Peng values) is used. -/
namespace Checked.Trust.SecondReading
/-- Peng and Robinson (1976): κ as a function of the acentric factor ω. -/
noncomputable def kappaPR76 (ω : ℝ) : ℝ := 0.37464 + 1.54226 * ω - 0.26992 * ω ^ 2
/-- Robinson and Peng (1978) revision, branch for heavier components (ω above about 0.49). -/
noncomputable def kappaPR78 (ω : ℝ) : ℝ := 0.379642 + 1.48503 * ω - 0.164423 * ω ^ 2 + 0.016666 * ω ^ 3
/-- Soave (1972) for the Soave–Redlich–Kwong equation: the coefficient m (also written κ) as a function of ω. -/
noncomputable def kappaSoave (ω : ℝ) : ℝ := 0.480 + 1.574 * ω - 0.176 * ω ^ 2
end Checked.Trust.SecondReading
