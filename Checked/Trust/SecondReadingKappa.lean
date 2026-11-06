import Mathlib.Data.Real.Basic
/-! Blind literal reading of three κ(ω) correlations (run 2026-11-06T0228Z). Copied verbatim (code) from `runs/2026-11-06T0228Z/kappa_reader/SecondReadingKappa.lean`, written by a blind reader (Sonnet subagent) from the brief committed before it in that folder. Sources: Reaktoro CubicEOS EquationModel API page; Cantera PengRobinson.h doxygen page; IDAES cubic EoS docs (secondary sources, not the primary papers). The Cantera page prints different digits in two coefficients of the PR78 heavy branch; the reader used Reaktoro's (its original note is in the runs/ copy). -/
namespace Checked.Trust.SecondReading
/-- Peng and Robinson (1976): κ as a function of the acentric factor ω. -/
noncomputable def kappaPR76 (ω : ℝ) : ℝ := 0.37464 + 1.54226 * ω - 0.26992 * ω ^ 2
/-- Robinson and Peng (1978) revision, branch for heavier components (ω above about 0.49). -/
noncomputable def kappaPR78 (ω : ℝ) : ℝ := 0.379642 + 1.48503 * ω - 0.164423 * ω ^ 2 + 0.016666 * ω ^ 3
/-- Soave (1972) for the Soave–Redlich–Kwong equation: the coefficient m (also written κ) as a function of ω. -/
noncomputable def kappaSoave (ω : ℝ) : ℝ := 0.480 + 1.574 * ω - 0.176 * ω ^ 2
end Checked.Trust.SecondReading
