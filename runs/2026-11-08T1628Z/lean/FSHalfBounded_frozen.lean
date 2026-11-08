import Checked.FalknerSkan.Bounded
import Checked.FalknerSkan.FSScale
/-! Falkner–Skan β = 1/2 in the class −1 ≤ f' ≤ 1: every solution of the boundary-value problem whose velocity profile is bounded by one in absolute value on the closed half-line has its wall shear inside the window of the statement, any two such solutions are equal on the closed half-line, and a solution with velocity profile in the half-open unit interval exists. Obtained from the Homann theorems of `Checked.FalknerSkan.Bounded` by the similarity scaling of `Checked.FalknerSkan.FSScale` with c the reciprocal of the square root of two. -/

namespace Checked.FalknerSkan.HalfBounded
open Set Filter Topology

/-- Falkner–Skan β = 1/2: every solution of f''' + f f'' + (1 − f'²)/2 = 0 on [0, ∞) (f has
derivative p, p has derivative q, q has derivative −f q − (1 − p²)/2, one-sided at 0) with
f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞ and −1 ≤ p ≤ 1 on [0, ∞) has wall shear q(0) = f''(0)
strictly between 0.927680039 and 0.927680040. -/
theorem fs_half_bounded_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 2 * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) :
    0.927680039 < q 0 ∧ q 0 < 0.927680040 := by
  sorry

/-- Falkner–Skan β = 1/2: for every solution (f, p, q) and every solution (f₂, p₂, q₂) of
f''' + f f'' + (1 − f'²)/2 = 0 on [0, ∞) (derivatives one-sided at 0), both with f(0) = 0,
p(0) = 0, p(η) → 1 as η → ∞ and −1 ≤ p ≤ 1 on [0, ∞): f η = f₂ η, p η = p₂ η and q η = q₂ η for
every η ≥ 0. -/
theorem fs_half_bounded_equal (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 2 * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1)
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - 1 / 2 * (1 - p₂ η ^ 2)) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1))
    (hb₂ : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p₂ η ∧ p₂ η ≤ 1) :
    ∀ η ∈ Ici (0 : ℝ), f η = f₂ η ∧ p η = p₂ η ∧ q η = q₂ η := by
  sorry

/-- Falkner–Skan β = 1/2: there is a solution of f''' + f f'' + (1 − f'²)/2 = 0 on [0, ∞)
(f has derivative p, p has derivative q, q has derivative −f q − (1 − p²)/2, one-sided at 0) with
f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞, 0 ≤ p < 1 on [0, ∞), and wall shear q(0) = f''(0)
strictly between 0.927680039 and 0.927680040. -/
theorem fs_half_exists_bounded : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 2 * (1 - p η ^ 2)) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧ (∀ η ∈ Ici (0 : ℝ), 0 ≤ p η ∧ p η < 1) ∧
    0.927680039 < q 0 ∧ q 0 < 0.927680040 := by
  sorry

end Checked.FalknerSkan.HalfBounded
