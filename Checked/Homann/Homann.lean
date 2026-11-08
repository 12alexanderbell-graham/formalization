import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Checked.Homann.HmUData
import Checked.Homann.HmOData
import Checked.Homann.HmExAssemble
/-! Homann stagnation-point flow, `Homann`: the Homann axisymmetric stagnation-point flow: the two shooting events at the ends of the wall-shear window printed in the statements of `homann_under` and `homann_over`, and existence of a solution of the boundary-value problem with wall shear in that window (`homann_exists`); uniqueness of that solution is not formalised. Promoted from `Work/Homann/Homann.lean`. -/

namespace Checked.Homann
open Set Filter Topology

/-- Homann axisymmetric stagnation-point flow, undershoot: for every S ≥ 6 and every solution of
f''' + 2 f f'' + 1 − f'² = 0 on [0, S] (f has derivative p, p has derivative q, q has derivative
−2 f q − 1 + p², within [0, S]) with f(0) = 0, p(0) = 0 and q(0) = 1.3119376938, there is
η in (0, 6] with q(η) < 0 and p < 1 on [0, η]. -/
theorem homann_under (S : ℝ) (hS : 6 ≤ S) (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt f (p η) (Icc 0 S) η)
    (hp : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt p (q η) (Icc 0 S) η)
    (hq : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt q (-(2 * f η * q η) - 1 + p η ^ 2) (Icc 0 S) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hq0 : q 0 = 1.3119376938) :
    ∃ η ∈ Ioc (0 : ℝ) 6, q η < 0 ∧ ∀ s ∈ Icc 0 η, p s < 1 := by
  have hsub : Icc (0 : ℝ) 6 ⊆ Icc 0 S := Icc_subset_Icc le_rfl hS
  obtain ⟨hq', hp'⟩ := Checked.Homann.HmUData.chain (g := f) (p := p) (q := q)
    (fun t ht => (hf t (hsub ht)).mono hsub) (fun t ht => (hp t (hsub ht)).mono hsub)
    (fun t ht => (hq t (hsub ht)).mono hsub) hf0 hp0 hq0
  exact ⟨6, ⟨by norm_num, le_rfl⟩, hq', hp'⟩

/-- Homann axisymmetric stagnation-point flow, overshoot: for every S ≥ 6 and every solution of
f''' + 2 f f'' + 1 − f'² = 0 on [0, S] (f has derivative p, p has derivative q, q has derivative
−2 f q − 1 + p², within [0, S]) with f(0) = 0, p(0) = 0 and q(0) = 1.3119376939, there is
η in (0, 6] with p(η) > 1 and q > 0 on [0, η]. -/
theorem homann_over (S : ℝ) (hS : 6 ≤ S) (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt f (p η) (Icc 0 S) η)
    (hp : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt p (q η) (Icc 0 S) η)
    (hq : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt q (-(2 * f η * q η) - 1 + p η ^ 2) (Icc 0 S) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hq0 : q 0 = 1.3119376939) :
    ∃ η ∈ Ioc (0 : ℝ) 6, 1 < p η ∧ ∀ s ∈ Icc 0 η, 0 < q s := by
  have hsub : Icc (0 : ℝ) 6 ⊆ Icc 0 S := Icc_subset_Icc le_rfl hS
  obtain ⟨hp', hq'⟩ := Checked.Homann.HmOData.chain (g := f) (p := p) (q := q)
    (fun t ht => (hf t (hsub ht)).mono hsub) (fun t ht => (hp t (hsub ht)).mono hsub)
    (fun t ht => (hq t (hsub ht)).mono hsub) hf0 hp0 hq0
  exact ⟨6, ⟨by norm_num, le_rfl⟩, hp', hq'⟩

/-- Homann axisymmetric stagnation-point flow, existence: there is a solution of
f''' + 2 f f'' + 1 − f'² = 0 on [0, ∞) (f has derivative p, p has derivative q, q has derivative
−2 f q − 1 + p², one-sided at 0) with f(0) = 0, p(0) = 0 and p(η) → 1 as η → ∞ whose wall value
q(0) = f''(0) lies strictly between 1.3119376938 and 1.3119376939. -/
theorem homann_exists : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(2 * f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    1.3119376938 < q 0 ∧ q 0 < 1.3119376939 :=
  Checked.Homann.HmExAssemble.exists_bvp

end Checked.Homann
