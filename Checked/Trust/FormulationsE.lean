import Checked.Trust.SecondFormulationE
import Checked.Trust.Formulations

/-!
# The marginalised chi-square agrees with a blind second formulation for every prior width (run 2026-11-05T2028Z)

The right-hand side is `Checked/Trust/SecondFormulationE.lean`, copied verbatim from
`runs/2026-11-05T2028Z/blind_formulation/SecondFormulationE.lean`, written by a Sonnet subagent from the
brief `runs/2026-11-05T2028Z/blind_formulation/briefE.md` (the prior's standard deviation is |σ|, so
the density is normalised for either sign of σ). The earlier blind formulation agreed only for σ > 0
(`Checked.Trust.FormulationsCond.agree_margChiSq_pos`); this one agrees for every σ, including the
junk value at σ = 0.
-/

namespace Checked.Trust.Formulations

/-- `Checked.Data.FR13.margChiSq` agrees with the blind second formulation E. -/
theorem agree_margChiSq : @Checked.Data.FR13.margChiSq = @Checked.Trust.SecondFormulationE.margChiSq := by
  funext n tbl Hbar σ Ω
  have hs : √(2 * Real.pi * σ ^ 2) = √(2 * Real.pi) * |σ| := by
    rw [Real.sqrt_mul (by positivity) (σ ^ 2), Real.sqrt_sq_eq_abs]
  unfold Checked.Data.FR13.margChiSq Checked.Trust.SecondFormulationE.margChiSq
  rw [Checked.Trust.Formulations.agree_chiSqHz, hs]
  congr 2
  congr 1
  funext H₀
  ring

end Checked.Trust.Formulations
