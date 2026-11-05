import Checked.Trust.Formulations

/-!
# A blind second formulation that agrees only on the physical domain (run 2026-11-05T0828Z)

`Checked.Data.FR13.margChiSq` normalises the Gaussian prior by `√(2πσ²)` (= `|σ|√(2π)`); the blind
second formulation (`Checked.Trust.SecondFormulation.margChiSq`) by `σ√(2π)`. They differ for
`σ < 0`, where neither is a standard deviation, and agree for every `σ > 0` (proved here). The
definition therefore stays in `scripts/trust/formula_baseline.txt` (an agreement of constants is
not available); every headline that uses it fixes `σ` to a positive printed value.
-/

namespace Checked.Trust.FormulationsCond

/-- For a positive prior width the program's marginalised chi-square equals the blind second
formulation. -/
theorem agree_margChiSq_pos {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (Hbar σ Ω : ℝ) (hσ : 0 < σ) :
    Checked.Data.FR13.margChiSq tbl Hbar σ Ω = Checked.Trust.SecondFormulation.margChiSq tbl Hbar σ Ω := by
  have hs : √(2 * Real.pi * σ ^ 2) = σ * √(2 * Real.pi) := by
    rw [show 2 * Real.pi * σ ^ 2 = σ ^ 2 * (2 * Real.pi) by ring, Real.sqrt_mul (sq_nonneg σ),
      Real.sqrt_sq hσ.le]
  unfold Checked.Data.FR13.margChiSq Checked.Trust.SecondFormulation.margChiSq
  rw [Checked.Trust.Formulations.agree_chiSqHz, hs]

end Checked.Trust.FormulationsCond
