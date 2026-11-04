import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Copied verbatim by script from `Work/Trust/SecondReadingL19.lean` (run 2026-11-04T1228Z). Blind second reading of Lusso et al. 2019 Eq. (7) (arXiv:1907.07692v4, p. 3), from the reader's own render. -/

namespace Checked.Trust.SecondReading.L19

/-- Lusso et al. 2019, Eq. (7): D_L(z) = k ln(10) (c/H₀) × [log(1+z) + a₂ log²(1+z)
+ a₃ log³(1+z) + a₄ log⁴(1+z)] + O[log⁵(1+z)], with c = 1, k = 1, log = log₁₀,
remainder dropped. -/
noncomputable def logPolyDL4 (a₂ a₃ a₄ H₀ z : ℝ) : ℝ :=
  Real.log 10 * (1 / H₀) *
    (Real.logb 10 (1 + z) + a₂ * Real.logb 10 (1 + z) ^ 2 + a₃ * Real.logb 10 (1 + z) ^ 3
      + a₄ * Real.logb 10 (1 + z) ^ 4)

end Checked.Trust.SecondReading.L19
