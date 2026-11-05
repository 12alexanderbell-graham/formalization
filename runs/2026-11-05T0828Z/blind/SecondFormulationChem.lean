import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
namespace Checked.Trust.SecondFormulation

/-- Pressure of the generalized two-parameter cubic equation of state:
`P = R T / (v - b) - a / (v² + u b v + w b²)`.  Repulsive ideal-gas-with-co-volume term minus an
attraction term; `(u,w) = (0,0)` is van der Waals, `(1,0)` Redlich–Kwong, `(2,-1)` Peng–Robinson. -/
noncomputable def cubicP (R a b u w T v : ℝ) : ℝ :=
  R * T / (v - b) - a / (v ^ 2 + u * b * v + w * b ^ 2)

/-- Critical-point cubic in `x = v_c / b`, monic.  Derived with sympy: set `∂P/∂v = 0`, solve for
`R T`, substitute in `∂²P/∂v² = 0` (with `b = 1`, `D = x² + u x + w`); the numerator is
`-2a (x³ - 3x² - 3(u+w)x - (u² + u w - w))`, hence the monic polynomial
`x³ - 3x² - 3(u+w)x - (u² + u w - w)`.  For van der Waals it is `x³ - 3x²`, root `x = 3`. -/
def critCubic (u w x : ℝ) : ℝ :=
  x ^ 3 - 3 * x ^ 2 - 3 * (u + w) * x - (u ^ 2 + u * w - w)

/-- Pitzer's acentric factor `ω = -log₁₀(P_sat(T_r = 0.7) / P_c) - 1`. -/
noncomputable def acentric (ps pc : ℝ) : ℝ :=
  -(Real.logb 10 (ps / pc)) - 1

/-- Chi-square of flat ΛCDM `H(z) = H₀ √(Ω (1+z)³ + 1 - Ω)` against data rows `(z, H, σ)`:
`Σᵢ ((Hᵢ - H(zᵢ)) / σᵢ)²` (uncorrelated Gaussian errors). -/
noncomputable def chiSqHz {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (H₀ Ω : ℝ) : ℝ :=
  ∑ i : Fin n,
    (((tbl i).2.1 - H₀ * √(Ω * (1 + (tbl i).1) ^ 3 + (1 - Ω))) / (tbl i).2.2) ^ 2

/-- Marginalised chi-square: `-2 ln ∫ exp(-χ²(H₀,Ω)/2) · N(H₀; Hbar, σ²) dH₀`, with the normalised
Gaussian prior density `exp(-(H₀-Hbar)²/(2σ²)) / (σ √(2π))`, integrated over all reals. -/
noncomputable def margChiSq {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (Hbar σ Ω : ℝ) : ℝ :=
  -2 * Real.log (∫ H₀ : ℝ, Real.exp (-(chiSqHz tbl H₀ Ω) / 2) *
    (Real.exp (-((H₀ - Hbar) ^ 2) / (2 * σ ^ 2)) / (σ * √(2 * Real.pi))))

end Checked.Trust.SecondFormulation
