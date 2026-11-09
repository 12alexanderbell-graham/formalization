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
import Checked.FalknerSkan.NegCore

/-! Falkner–Skan with adverse pressure gradient: in the class of solutions with positive second derivative that approach the edge value faster than every exponential, the wall shear is the largest and two solutions are equal. Module `NegDecay`, promoted from `Work/FalknerSkan/NegDecay.lean`. -/

namespace Checked.FalknerSkan.NegDecay

open Set Filter Topology

/-- Falkner–Skan with β < 0: if (f, p, q) is a solution of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with
f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`, and (f₂, p₂, q₂) is a
solution with f₂(0) = 0, p₂(0) = 0, p₂ → 1 and q₂ > 0 on [0, ∞), then q₂(0) ≤ q(0). -/
theorem fs_neg_decay_max_shear (β : ℝ) (hβ : β < 0) (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η)
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - β * (1 - p₂ η ^ 2)) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1))
    (hpos₂ : ∀ η ∈ Ici (0 : ℝ), 0 < q₂ η) :
    q₂ 0 ≤ q 0 := by
  have hc : 0 < Real.sqrt (-β) := Real.sqrt_pos.2 (by linarith)
  have hK : (0 : ℝ) < 1 / (-β) := one_div_pos.2 (by linarith)
  have h := Checked.FalknerSkan.NegUPrime.u_prime hK
    (Checked.FalknerSkan.NegCore.toSol hβ hf hp hq hf0 hp0 hlim hpos)
    (Checked.FalknerSkan.NegCore.toSol hβ hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hpos₂)
    (Checked.FalknerSkan.NegCore.toDec hβ hdec)
  simp only [zero_div] at h
  exact (div_le_div_iff_of_pos_right hc).1 h

/-- Falkner–Skan with β < 0: for every solution (f, p, q) and every solution (f₂, p₂, q₂) of
f''' + f f'' + β(1 − f'²) = 0 on [0, ∞), both with f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and,
for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`: f η = f₂ η, p η = p₂ η and q η = q₂ η for every η ≥ 0. -/
theorem fs_neg_decay_equal (β : ℝ) (hβ : β < 0) (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η)
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - β * (1 - p₂ η ^ 2)) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1))
    (hpos₂ : ∀ η ∈ Ici (0 : ℝ), 0 < q₂ η)
    (hdec₂ : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p₂ η) ≤ q₂ η) :
    ∀ η ∈ Ici (0 : ℝ), f η = f₂ η ∧ p η = p₂ η ∧ q η = q₂ η := by
  have h1 := fs_neg_decay_max_shear β hβ f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hpos hdec
    hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hpos₂
  have h2 := fs_neg_decay_max_shear β hβ f₂ p₂ q₂ f p q hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hpos₂ hdec₂
    hf hp hq hf0 hp0 hlim hpos
  exact Checked.FalknerSkan.NegCore.eq_of_startb hf hp hq hf₂ hp₂ hq₂ (by rw [hf0, hf₂0])
    (by rw [hp0, hp₂0]) (le_antisymm h2 h1)

end Checked.FalknerSkan.NegDecay
