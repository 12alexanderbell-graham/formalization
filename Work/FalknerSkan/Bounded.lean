import Checked.FalknerSkan.MonotoneWindow
import Checked.FalknerSkan.MonotoneExists
import Work.FalknerSkan.BoundedTools

/-!
# Hiemenz and Homann: the solution with −1 ≤ f' ≤ 1 (window, uniqueness, existence)

Frozen statements (run 2026-11-08T1228Z), before any proof. Hiemenz: f''' + f f'' + 1 − f'² = 0;
Homann: f''' + 2 f f'' + 1 − f'² = 0; f(0) = f'(0) = 0, f'(η) → 1 as η → ∞; first-order system
f' = p, p' = q with derivatives within [0, ∞) (one-sided at 0).

The checked theorems `Checked.FalknerSkan.MonotoneWindow.hiemenz_monotone_window` (and Homann)
assume f'' > 0 on [0, ∞), a condition on the unknown's second derivative. Here the hypothesis is
the bound −1 ≤ f' ≤ 1 on [0, ∞) instead (it contains the class 0 < f' < 1 of the classical
uniqueness theory; whether f' < 1 alone suffices is not settled here).

* `hiemenz_bounded_window`, `homann_bounded_window`: every such solution has its wall shear in the
  certified window.
* `hiemenz_bounded_unique`, `homann_bounded_unique`: any two such solutions are equal on [0, ∞).
* `hiemenz_exists_bounded`, `homann_exists_bounded`: there is a solution with 0 ≤ f' < 1 on
  [0, ∞) and wall shear in the window.

Planned proofs: `Work.FalknerSkan.BoundedTools` turns −1 ≤ p ≤ 1 into q > 0; then the monotone
window, the Crocco comparison `Checked.FalknerSkan.MonotoneExists.not_lt_wall` (same wall shear)
and forward uniqueness from the start values; existence from the monotone solution.
-/

namespace Work.FalknerSkan.Bounded
open Set Filter Topology

/-- Hiemenz stagnation-point flow: every solution of f''' + f f'' + 1 − f'² = 0 on [0, ∞)
(f has derivative p, p has derivative q, q has derivative −f q − 1 + p², one-sided at 0) with
f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞ and −1 ≤ p ≤ 1 on [0, ∞) has wall shear q(0) = f''(0)
strictly between 1.2325876568 and 1.2325876569. -/
theorem hiemenz_bounded_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) :
    1.2325876568 < q 0 ∧ q 0 < 1.2325876569 := by
  sorry

/-- Homann axisymmetric stagnation-point flow: every solution of f''' + 2 f f'' + 1 − f'² = 0 on
[0, ∞) (f has derivative p, p has derivative q, q has derivative −2 f q − 1 + p², one-sided at 0)
with f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞ and −1 ≤ p ≤ 1 on [0, ∞) has wall shear
q(0) = f''(0) strictly between 1.3119376938 and 1.3119376939. -/
theorem homann_bounded_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(2 * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) :
    1.3119376938 < q 0 ∧ q 0 < 1.3119376939 := by
  sorry

/-- Hiemenz stagnation-point flow: any two solutions of f''' + f f'' + 1 − f'² = 0 on [0, ∞)
(derivatives one-sided at 0) with f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞ and −1 ≤ p ≤ 1 on
[0, ∞) are equal on [0, ∞): same f, same p = f', same q = f''. -/
theorem hiemenz_bounded_unique (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1)
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - 1 + p₂ η ^ 2) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1))
    (hb₂ : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p₂ η ∧ p₂ η ≤ 1) :
    ∀ η ∈ Ici (0 : ℝ), f η = f₂ η ∧ p η = p₂ η ∧ q η = q₂ η := by
  sorry

/-- Homann axisymmetric stagnation-point flow: any two solutions of f''' + 2 f f'' + 1 − f'² = 0
on [0, ∞) (derivatives one-sided at 0) with f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞ and
−1 ≤ p ≤ 1 on [0, ∞) are equal on [0, ∞): same f, same p = f', same q = f''. -/
theorem homann_bounded_unique (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(2 * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1)
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(2 * f₂ η * q₂ η) - 1 + p₂ η ^ 2) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1))
    (hb₂ : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p₂ η ∧ p₂ η ≤ 1) :
    ∀ η ∈ Ici (0 : ℝ), f η = f₂ η ∧ p η = p₂ η ∧ q η = q₂ η := by
  sorry

/-- Hiemenz stagnation-point flow: there is a solution of f''' + f f'' + 1 − f'² = 0 on [0, ∞)
(f has derivative p, p has derivative q, q has derivative −f q − 1 + p², one-sided at 0) with
f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞, 0 ≤ p < 1 on [0, ∞), and wall shear q(0) = f''(0)
strictly between 1.2325876568 and 1.2325876569. -/
theorem hiemenz_exists_bounded : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧ (∀ η ∈ Ici (0 : ℝ), 0 ≤ p η ∧ p η < 1) ∧
    1.2325876568 < q 0 ∧ q 0 < 1.2325876569 := by
  sorry

/-- Homann axisymmetric stagnation-point flow: there is a solution of f''' + 2 f f'' + 1 − f'² = 0
on [0, ∞) (f has derivative p, p has derivative q, q has derivative −2 f q − 1 + p², one-sided at
0) with f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞, 0 ≤ p < 1 on [0, ∞), and wall shear
q(0) = f''(0) strictly between 1.3119376938 and 1.3119376939. -/
theorem homann_exists_bounded : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(2 * f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧ (∀ η ∈ Ici (0 : ℝ), 0 ≤ p η ∧ p η < 1) ∧
    1.3119376938 < q 0 ∧ q 0 < 1.3119376939 := by
  sorry

end Work.FalknerSkan.Bounded
