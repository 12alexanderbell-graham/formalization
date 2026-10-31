import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Blind second reading of the B1 printed definitions (run 2026-10-31T0428Z): copied verbatim by
script from `Work/Trust/SecondReadingB1.lean` (subagent read only the typeset crops / its own
renders of arXiv 1907.07692 and 1811.02590). -/

namespace Checked.Trust.SecondReading.B1

/-- Lusso et al. 2019, Eq. (8): a₂ = ln(10) × (3/2 − (3/4) Ω_M). -/
noncomputable def lusA2 (Ω : ℝ) : ℝ :=
  Real.log 10 * (3 / 2 - 3 / 4 * Ω)

/-- Lusso et al. 2019, Eq. (8): a₃ = ln²(10) × ((9/8) Ω_M² − 2 Ω_M + 7/6). -/
noncomputable def lusA3 (Ω : ℝ) : ℝ :=
  Real.log 10 ^ 2 * (9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6)

/-- Risaliti & Lusso 2019, Methods: D_L = ln(10) c/H₀ (x + a₂x² + a₃x³), x = log(1+z), c = 1. -/
noncomputable def logPolyDL3 (a₂ a₃ H₀ z : ℝ) : ℝ :=
  Real.log 10 * (1 / H₀) *
    (Real.logb 10 (1 + z) + a₂ * Real.logb 10 (1 + z) ^ 2 + a₃ * Real.logb 10 (1 + z) ^ 3)

end Checked.Trust.SecondReading.B1
