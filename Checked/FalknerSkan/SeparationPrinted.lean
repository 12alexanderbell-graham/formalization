import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Order.IntermediateValue
import Checked.FSSep.UPair
import Checked.FalknerSkan.Separation
import Checked.FalknerSkan.SeparationEqual

/-! Falkner–Skan separation: the parameter of every zero-wall-shear solution approaching the edge value faster than every exponential lies below the value printed by Fazio for the limiting parameter. Module `SeparationPrinted`, written run 2026-11-11T0828Z as a corollary of `Separation` and `SeparationEqual`. -/

namespace Checked.FalknerSkan.SeparationPrinted

open Set Filter Topology

/-- Falkner–Skan separation: for every solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with f(0) = 0,
p(0) = 0, wall shear q(0) = 0, p → 1, q > 0 on (0, ∞) and, for every M,
`∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`: β < `-(1988376 / 10000000)`, so β lies below the value Fazio
printed for the parameter of the solution with zero wall shear. -/
theorem fs_separation_below_printed {β : ℝ} {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hq0 : q 0 = 0) (hl : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ioi (0 : ℝ), 0 < q η) (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :
    β < -(1988376 / 10000000) := by
  obtain ⟨β₀, hw, f₀, p₀, q₀, hf₀, hp₀, hq₀, hf₀0, hp₀0, hq₀0, hl₀, hpos₀, hdec₀⟩ :=
    Checked.FalknerSkan.Separation.fs_separation_exists
  have e := Checked.FalknerSkan.SeparationEqual.fs_separation_equal hf hp hq hf0 hp0 hq0 hl hpos hdec
    hf₀ hp₀ hq₀ hf₀0 hp₀0 hq₀0 hl₀ hpos₀ hdec₀
  rw [e]
  have h2 := hw.2
  linarith

end Checked.FalknerSkan.SeparationPrinted

#print axioms Checked.FalknerSkan.SeparationPrinted.fs_separation_below_printed
