import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Checked.Hiemenz.HUData
import Checked.Hiemenz.HOData
import Checked.Hiemenz.HExAssemble
/-! Hiemenz stagnation-point flow, `Hiemenz`: the Hiemenz stagnation-point flow: the two shooting events at the ends of the wall-shear window printed in the statements of `hiemenz_under` and `hiemenz_over`, and existence of a solution of the boundary-value problem with wall shear in that window (`hiemenz_exists`); uniqueness of that solution is not formalised. Promoted from `Work/Hiemenz/Hiemenz.lean`. -/

namespace Checked.Hiemenz
open Set Filter Topology

/-- Hiemenz stagnation-point flow, undershoot: for every S ≥ 15/2 and every solution of
f''' + f f'' + 1 − f'² = 0 on [0, S] (f has derivative p, p has derivative q, q has derivative
−f q − 1 + p², within [0, S]) with f(0) = 0, p(0) = 0 and q(0) = 1.2325876568, there is
η in (0, 15/2] with q(η) < 0 and p < 1 on [0, η]. -/
theorem hiemenz_under (S : ℝ) (hS : 15 / 2 ≤ S) (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt f (p η) (Icc 0 S) η)
    (hp : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt p (q η) (Icc 0 S) η)
    (hq : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Icc 0 S) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hq0 : q 0 = 1.2325876568) :
    ∃ η ∈ Ioc (0 : ℝ) (15 / 2), q η < 0 ∧ ∀ s ∈ Icc 0 η, p s < 1 := by
  have hsub : Icc (0 : ℝ) (15 / 2) ⊆ Icc 0 S := Icc_subset_Icc le_rfl hS
  obtain ⟨hq', hp'⟩ := Checked.Hiemenz.HUData.chain (g := f) (p := p) (q := q)
    (fun t ht => (hf t (hsub ht)).mono hsub) (fun t ht => (hp t (hsub ht)).mono hsub)
    (fun t ht => (hq t (hsub ht)).mono hsub) hf0 hp0 hq0
  exact ⟨15 / 2, ⟨by norm_num, le_rfl⟩, hq', hp'⟩

/-- Hiemenz stagnation-point flow, overshoot: for every S ≥ 15/2 and every solution of
f''' + f f'' + 1 − f'² = 0 on [0, S] (f has derivative p, p has derivative q, q has derivative
−f q − 1 + p², within [0, S]) with f(0) = 0, p(0) = 0 and q(0) = 1.2325876569, there is
η in (0, 15/2] with p(η) > 1 and q > 0 on [0, η]. -/
theorem hiemenz_over (S : ℝ) (hS : 15 / 2 ≤ S) (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt f (p η) (Icc 0 S) η)
    (hp : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt p (q η) (Icc 0 S) η)
    (hq : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Icc 0 S) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hq0 : q 0 = 1.2325876569) :
    ∃ η ∈ Ioc (0 : ℝ) (15 / 2), 1 < p η ∧ ∀ s ∈ Icc 0 η, 0 < q s := by
  have hsub : Icc (0 : ℝ) (15 / 2) ⊆ Icc 0 S := Icc_subset_Icc le_rfl hS
  obtain ⟨hp', hq'⟩ := Checked.Hiemenz.HOData.chain (g := f) (p := p) (q := q)
    (fun t ht => (hf t (hsub ht)).mono hsub) (fun t ht => (hp t (hsub ht)).mono hsub)
    (fun t ht => (hq t (hsub ht)).mono hsub) hf0 hp0 hq0
  exact ⟨15 / 2, ⟨by norm_num, le_rfl⟩, hp', hq'⟩

/-- Hiemenz stagnation-point flow, existence: there is a solution of f''' + f f'' + 1 − f'² = 0
on [0, ∞) (f has derivative p, p has derivative q, q has derivative −f q − 1 + p², one-sided
at 0) with f(0) = 0, p(0) = 0 and p(η) → 1 as η → ∞ whose wall value q(0) = f''(0) lies
strictly between 1.2325876568 and 1.2325876569. -/
theorem hiemenz_exists : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    1.2325876568 < q 0 ∧ q 0 < 1.2325876569 :=
  Checked.Hiemenz.HExAssemble.exists_bvp

end Checked.Hiemenz
