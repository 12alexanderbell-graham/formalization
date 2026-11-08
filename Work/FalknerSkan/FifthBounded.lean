import Mathlib
/-!
# Falkner–Skan β = 1/5 in the class −1 ≤ f' ≤ 1: window, uniqueness, existence (frozen before proof, run 2026-11-08T2028Z)

**Question.** The Falkner–Skan wedge-flow equation f''' + f f'' + β (1 − f'²) = 0, f(0) = f'(0) = 0,
f'(η) → 1, at the classical table row β = 1/5 (wedge half-angle π/10; tables print f''(0) ≈ 0.686708).
Is there a solution, is it the only one whose velocity profile stays in [−1, 1], and where exactly is its
wall shear?

**Statements** (p = f', q = f'', derivatives within the closed half-line):
* `fs_fifth_bounded_window`: every solution with −1 ≤ p ≤ 1 on [0, ∞) has 0.6867081809 < q(0) < 0.6867081811;
* `fs_fifth_bounded_equal`: two such solutions agree (f, p, q) on [0, ∞);
* `fs_fifth_exists_bounded`: such a solution exists, with 0 ≤ p < 1 on [0, ∞) and q(0) in the window.

**Planned route.** The scaling F(s) = c f(s/c) with c = 1/√5 turns the equation into
F''' + 5 F F'' + 1 − F'² = 0 (`Checked.FalknerSkan.FSScale.scale`), keeps p and the class and multiplies the
wall shear by √5. The coefficient-5 problem gets the route of the Homann row (coefficient 2): certified
shooting events at 1.5355261734 and 1.5355261735 (`Work.FSFifth`, generated cells), the Crocco comparison for
the window and the equality, the shooting existence with q > 0.
-/

namespace Work.FalknerSkan.FifthBounded
open Set Filter Topology

/-- Falkner–Skan β = 1/5: every solution of f''' + f f'' + (1 − f'²)/5 = 0 on [0, ∞) (f has
derivative p, p has derivative q, q has derivative −f q − (1 − p²)/5, one-sided at 0) with
f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞ and −1 ≤ p ≤ 1 on [0, ∞) has wall shear q(0) = f''(0)
strictly between 0.6867081809 and 0.6867081811. -/
theorem fs_fifth_bounded_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 5 * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) :
    0.6867081809 < q 0 ∧ q 0 < 0.6867081811 := by
  sorry

/-- Falkner–Skan β = 1/5: for every solution (f, p, q) and every solution (f₂, p₂, q₂) of
f''' + f f'' + (1 − f'²)/5 = 0 on [0, ∞) (derivatives one-sided at 0), both with f(0) = 0,
p(0) = 0, p(η) → 1 as η → ∞ and −1 ≤ p ≤ 1 on [0, ∞): f η = f₂ η, p η = p₂ η and q η = q₂ η for
every η ≥ 0. -/
theorem fs_fifth_bounded_equal (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 5 * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1)
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - 1 / 5 * (1 - p₂ η ^ 2)) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1))
    (hb₂ : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p₂ η ∧ p₂ η ≤ 1) :
    ∀ η ∈ Ici (0 : ℝ), f η = f₂ η ∧ p η = p₂ η ∧ q η = q₂ η := by
  sorry

/-- Falkner–Skan β = 1/5: there is a solution of f''' + f f'' + (1 − f'²)/5 = 0 on [0, ∞)
(f has derivative p, p has derivative q, q has derivative −f q − (1 − p²)/5, one-sided at 0) with
f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞, 0 ≤ p < 1 on [0, ∞), and wall shear q(0) = f''(0)
strictly between 0.6867081809 and 0.6867081811. -/
theorem fs_fifth_exists_bounded : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 5 * (1 - p η ^ 2)) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧ (∀ η ∈ Ici (0 : ℝ), 0 ≤ p η ∧ p η < 1) ∧
    0.6867081809 < q 0 ∧ q 0 < 0.6867081811 := by
  sorry

end Work.FalknerSkan.FifthBounded
