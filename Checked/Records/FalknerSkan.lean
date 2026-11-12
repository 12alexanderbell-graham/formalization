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
import Checked.Records.Basic
import Checked.FalknerSkan.Separation
import Checked.FalknerSkan.SeparationEqual
import Checked.FalknerSkan.NegWallShear
import Checked.FalknerSkan.NegReversedWallShear

/-!
# Certified numbers of the verified findings F12–F14 (run 2026-11-12T1028Z)

The Falkner–Skan findings (candidates C-FS-SEP, C-FS-1988, C-FS-1988R until this run) refute published
values near separation. Their Lean evidence is the registered headlines of `Checked/FalknerSkan/`
(`fs_separation_exists`, `fs_separation_equal`, `fs_neg_wall_shear_window`, `fs_neg_reversed_wall_shear_exists`);
the records below certify the difference between each printed value (a PRINTED definition with a blind second
reading) and the quantity of every solution, as a rounding `RoundsTo x d k`, so that `FINDINGS.md` can show it in a
generated block next to the Lean statement. Hypotheses are copied verbatim from the headline they rest on (same
literals, same literal readings).
-/

namespace Checked.Records

open Set Filter Topology

/-- Fazio (arXiv:1212.5057, 2012, Fig. 4 caption; arXiv:2011.07725, 2020, Fig. 7 caption): the printed value of the
Falkner–Skan parameter of the solution with zero wall shear (blind second reading
`Checked.Trust.SecondReading.fsSepPrintedFazio`). -/
noncomputable def printedFazioSeparation : ℝ := -(1988376 / 10000000)

/-- Fazio (arXiv:1212.5057, 2012, p. 16): the printed missing initial condition d²f/dη²(0) of the normal-flow
Falkner–Skan solution at the example parameter (blind second reading
`Checked.Trust.SecondReading.fsAttPrintedWallValueFazio`). -/
noncomputable def printedFazioWall : ℝ := 0.005221

/-- Fazio (arXiv:1212.5057, 2012, p. 16): the printed missing initial condition d²f/dη²(0) of the reverse-flow
Falkner–Skan solution at the example parameter (blind second reading
`Checked.Trust.SecondReading.fsRevPrintedWallValueFazio`). -/
noncomputable def printedFazioRevWall : ℝ := -0.005158

/-! ## F12 (the Falkner–Skan separation parameter) -/

/-- Falkner–Skan separation: for every solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with f(0) = 0,
p(0) = 0, wall shear q(0) = 0, p → 1, q > 0 on (0, ∞) and, for every M,
`∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`, the value Fazio printed for that parameter
(`printedFazioSeparation`) minus β rounds to `0.00000014` at eight decimals. -/
theorem F12_separation {β : ℝ} {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hq0 : q 0 = 0) (hl : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ioi (0 : ℝ), 0 < q η) (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :
    RoundsTo (printedFazioSeparation - β) 0.00000014 8 := by
  obtain ⟨β₀, hw, f₀, p₀, q₀, hf₀, hp₀, hq₀, hf₀0, hp₀0, hq₀0, hl₀, hpos₀, hdec₀⟩ :=
    Checked.FalknerSkan.Separation.fs_separation_exists
  have e := Checked.FalknerSkan.SeparationEqual.fs_separation_equal hf hp hq hf0 hp0 hq0 hl hpos hdec
    hf₀ hp₀ hq₀ hf₀0 hp₀0 hq₀0 hl₀ hpos₀ hdec₀
  rw [e]
  obtain ⟨h1, h2⟩ := hw
  unfold RoundsTo printedFazioSeparation; rw [abs_le]; constructor <;> norm_num <;> linarith

/-! ## F13 (attached flow at β = −0.1988) -/

/-- Falkner–Skan with β = −1988/10000: if (f, p, q) is a solution of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞)
with f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`,
then the value Fazio printed for the normal-flow wall shear (`printedFazioWall`) minus q(0) rounds to `0.000003`
at six decimals. -/
theorem F13_wall_shear (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1988 / 10000) * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :
    RoundsTo (printedFazioWall - q 0) 0.000003 6 := by
  obtain ⟨h1, h2⟩ :=
    Checked.FalknerSkan.NegWallShear.fs_neg_wall_shear_window f p q hf hp hq hf0 hp0 hlim hpos hdec
  unfold RoundsTo printedFazioWall; rw [abs_le]; constructor <;> norm_num <;> linarith

/-! ## F14 (reversed flow at β = −0.1988) -/

/-- Falkner–Skan with β = −1988/10000: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with
f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`,
whose wall shear q(0) minus the reverse-flow value Fazio printed (`printedFazioRevWall`) rounds to `0.0000006` at
seven decimals. -/
theorem F14_reversed_wall_shear :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1988 / 10000) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      RoundsTo (q 0 - printedFazioRevWall) 0.0000006 7 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ :=
    Checked.FalknerSkan.NegReversedWallShear.fs_neg_reversed_wall_shear_exists
  refine ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, ?_⟩
  unfold RoundsTo printedFazioRevWall; rw [abs_le]; constructor <;> norm_num <;> linarith

end Checked.Records

#print axioms Checked.Records.F12_separation
#print axioms Checked.Records.F13_wall_shear
#print axioms Checked.Records.F14_reversed_wall_shear
