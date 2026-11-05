import Checked.Trust.SecondFormulation
namespace Checked.Trust.SecondFormulationE

/-- Marginalised chi-square over `H₀`: `-2 log ∫ N(H₀; Hbar, σ²) · exp(-χ²(H₀,Ω)/2) dH₀`,
with a normalised Gaussian prior density of mean `Hbar` and standard deviation `|σ|`. -/
noncomputable def margChiSq {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (Hbar σ Ω : ℝ) : ℝ :=
  -2 * Real.log (∫ H₀ : ℝ,
    (1 / (Real.sqrt (2 * Real.pi) * |σ|)) * Real.exp (-((H₀ - Hbar) ^ 2) / (2 * σ ^ 2))
      * Real.exp (-(Checked.Trust.SecondFormulation.chiSqHz tbl H₀ Ω) / 2))

end Checked.Trust.SecondFormulationE
