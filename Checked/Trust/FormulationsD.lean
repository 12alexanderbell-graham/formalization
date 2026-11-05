import Checked.Trust.SecondFormulationD
import Checked.Records.Basic
import Checked.Cosmography.FRCosmo

/-!
# Seven baselined definitions agree with a blind second formulation (run 2026-11-05T2028Z)

The right-hand sides are `Checked/Trust/SecondFormulationD.lean`, copied verbatim from
`runs/2026-11-05T2028Z/blind_formulation/SecondFormulationD.lean`, written by a Sonnet subagent from
the brief `runs/2026-11-05T2028Z/blind_formulation/briefD.md` (names, argument roles, conventions; the
correct F(R) denominator derived by it from the field equations with sympy). A failing proof would be
a disagreement to investigate, never an edit to make them agree.
-/

namespace Checked.Trust.Formulations

/-- `Checked.Records.RoundsTo` agrees with the blind second formulation. -/
theorem agree_RoundsTo : Checked.Records.RoundsTo = Checked.Trust.SecondFormulation.RoundsTo := by
  funext x d k
  simp only [Checked.Records.RoundsTo, Checked.Trust.SecondFormulation.RoundsTo]
  congr 1
  field_simp

/-- `Checked.Fidelity.coshBounce` agrees with the blind second formulation. -/
theorem agree_coshBounce : Checked.Fidelity.coshBounce = Checked.Trust.SecondFormulation.coshBounce := by
  funext t
  simp only [Checked.Fidelity.coshBounce, Checked.Trust.SecondFormulation.coshBounce]

/-- `Checked.Cosmography.FREta.eta20Of` agrees with the blind second formulation. -/
theorem agree_eta20Of : Checked.Cosmography.FREta.eta20Of = Checked.Trust.SecondFormulation.eta20Of := by
  funext Ω q j s l
  simp only [Checked.Cosmography.FREta.eta20Of, Checked.Trust.SecondFormulation.eta20Of]

/-- `Checked.Cosmography.FREta.eta30Of` agrees with the blind second formulation. -/
theorem agree_eta30Of : Checked.Cosmography.FREta.eta30Of = Checked.Trust.SecondFormulation.eta30Of := by
  funext Ω q j s l
  simp only [Checked.Cosmography.FREta.eta30Of, Checked.Trust.SecondFormulation.eta30Of]

/-- `Checked.Cosmography.FREta.Jfam` agrees with the blind second formulation. -/
theorem agree_Jfam : Checked.Cosmography.FREta.Jfam = Checked.Trust.SecondFormulation.Jfam := by
  funext Ω ε
  simp only [Checked.Cosmography.FREta.Jfam, Checked.Trust.SecondFormulation.Jfam]
  ring

/-- `Checked.Cosmography.BambaA.remA` agrees with the blind second formulation. -/
theorem agree_remA : Checked.Cosmography.BambaA.remA = Checked.Trust.SecondFormulation.remA := by
  funext D3 D4 K a t₀ t
  simp only [Checked.Cosmography.BambaA.remA, Checked.Trust.SecondFormulation.remA]

/-- `Checked.Cosmography.FRCosmo.correctR` agrees with the blind second formulation (the blind
formulator derived it from the field equations). -/
theorem agree_correctR : Checked.Cosmography.FRCosmo.correctR = Checked.Trust.SecondFormulation.correctR := by
  funext q j s l
  simp only [Checked.Cosmography.FRCosmo.correctR, Checked.Trust.SecondFormulation.correctR]
  ring

end Checked.Trust.Formulations
