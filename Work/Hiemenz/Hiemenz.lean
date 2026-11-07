import Mathlib
import Work.Hiemenz.HUData
import Work.Hiemenz.HOData

/-!
# Fluid mechanics (THE RESULT parts 2 and 5): the Hiemenz stagnation-point flow — two shooting
# events and existence (frozen before proof, run 2026-11-07T2028Z)

**Question.** Plane stagnation-point flow against a wall (Hiemenz 1911; the Falkner–Skan
equation with β = 1) reduces to the boundary-value problem
  f''' + f f'' + 1 − f'² = 0,  f(0) = f'(0) = 0,  f'(η) → 1 as η → ∞,
and the wall shear is f''(0). Printed values are floating point (f''(0) ≈ 1.2325876…). Unlike
Blasius, no scaling symmetry removes the far-field condition, so f''(0) is a genuine shooting
parameter.

**Statements.** Writing p = f' and q = f'' (derivatives within the interval, one-sided at the
ends):
* `hiemenz_under`: started with q(0) = 1.2325876568, every solution on [0, S] (S ≥ 15/2) has a
  point η ∈ (0, 15/2] where q(η) < 0 while p < 1 on [0, η] (the profile turns back below the
  outer velocity);
* `hiemenz_over`: started with q(0) = 1.2325876569, every solution has a point η ∈ (0, 15/2]
  where p(η) > 1 while q > 0 on [0, η] (the profile overshoots the outer velocity);
* `hiemenz_exists`: there is a solution on [0, ∞) of the boundary-value problem with
  1.2325876568 < f''(0) < 1.2325876569.

Uniqueness of the solution of the boundary-value problem (for 0 ≤ β ≤ 1 with no restriction
on f': Coppel 1960, Craven–Peletier 1972, as reported by the referee of run 2026-11-07T2028Z from
secondary surveys) is not formalised here; without it the two events say that the shooting values 1.2325876568 and
1.2325876569 do not give solutions with p ≤ 1 and q ≥ 0, and the existence theorem places a
solution between them.
-/

namespace Work.Hiemenz
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
  obtain ⟨hq', hp'⟩ := Work.Hiemenz.HUData.chain (g := f) (p := p) (q := q)
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
  obtain ⟨hp', hq'⟩ := Work.Hiemenz.HOData.chain (g := f) (p := p) (q := q)
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
    1.2325876568 < q 0 ∧ q 0 < 1.2325876569 := by
  sorry

end Work.Hiemenz
