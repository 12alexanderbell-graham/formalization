import Checked.Trust.SecondReadingM16
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Fin
namespace Checked.Trust.SecondFormulation

/-- Squared dimensionless expansion rate `E(z)² = (H(z)/H₀)²` of open ΛCDM (dust + Λ + curvature,
no radiation). Derived from the Friedmann equation
`H²/H₀² = Ωm(1+z)³ + Ωk(1+z)² + ΩΛ` with closure `Ωm + ΩΛ + Ωk = 1`, i.e. `Ωk = 1 - Ωm - ΩΛ`. -/
noncomputable def e2OL (Ωm ΩΛ z : ℝ) : ℝ :=
  Ωm * (1 + z) ^ 3 + (1 - Ωm - ΩΛ) * (1 + z) ^ 2 + ΩΛ

/-- χ² of `H(z) = H0 √(E²(z))` against the 30 rows `(z, H, σ)` of `m16Table`, i.e.
`Σ ((H_i - model(z_i))/σ_i)²`, plus the Gaussian prior on H0 (mean 73, sd 2.4) as one more term
`((H0 - 73)/2.4)²`. -/
noncomputable def chiSqOL (H0 Ωm ΩΛ : ℝ) : ℝ :=
  (∑ i : Fin 30,
      (((Checked.Trust.SecondReading.m16Table i).2.1
          - H0 * Real.sqrt (e2OL Ωm ΩΛ (Checked.Trust.SecondReading.m16Table i).1))
        / (Checked.Trust.SecondReading.m16Table i).2.2) ^ 2)
    + ((H0 - 73) / 2.4) ^ 2

/-- χ² of the line `f(z) = a + b z` against the rescaled data `H_i/(1+z_i)` with errors
`σ_i/(1+z_i)`, i.e. `Σ ((H_i/(1+z_i) - f(z_i)) / (σ_i/(1+z_i)))²`, plus the extra point
`f(0) = a` measured as 73 ± 2.4, i.e. `((a - 73)/2.4)²`. -/
noncomputable def chiSqLine (a b : ℝ) : ℝ :=
  (∑ i : Fin 30,
      (((Checked.Trust.SecondReading.m16Table i).2.1 / (1 + (Checked.Trust.SecondReading.m16Table i).1)
          - (a + b * (Checked.Trust.SecondReading.m16Table i).1))
        / ((Checked.Trust.SecondReading.m16Table i).2.2
            / (1 + (Checked.Trust.SecondReading.m16Table i).1))) ^ 2)
    + ((a + b * 0 - 73) / 2.4) ^ 2

end Checked.Trust.SecondFormulation
