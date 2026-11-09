import Checked.FalknerSkan.Bounded
import Checked.FalknerSkan.HalfBounded
import Checked.FalknerSkan.FifthBounded
/-! Falkner–Skan and stagnation-point boundary-value problems with no bound on the velocity profile
(run 2026-11-09T0028Z, frozen before proof): for 0 < β ≤ 1 every solution of
f''' + f f'' + β (1 − f'²) = 0 with f(0) = f'(0) = 0 and f' → 1 has f'' > 0 on the closed half-line,
so the window and equality theorems of the class −1 ≤ f' ≤ 1 hold for every solution of the
boundary-value problem. Proof plan: runs/2026-11-09T0028Z/coppel/REPORT.md. -/

namespace Work.FalknerSkan.Unrestricted
open Set Filter Topology

/-- Falkner–Skan with pressure-gradient coefficient β, 0 < β ≤ 1: every solution of
f''' + f f'' + β (1 − f'²) = 0 on [0, ∞) (f has derivative p, p has derivative q, q has derivative
−f q − β (1 − p²), one-sided at 0) with f(0) = 0, p(0) = 0 and p(η) → 1 as η → ∞ has q(η) = f''(η)
positive for every η ≥ 0. -/
theorem fs_monotone_of_limit (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)) :
    ∀ η ∈ Ici (0 : ℝ), 0 < q η := by
  sorry

/-- Hiemenz stagnation-point flow: every solution of f''' + f f'' + 1 − f'² = 0 on [0, ∞) (f has derivative p, p has
derivative q, q has derivative −f q − 1 + p², one-sided at 0) with f(0) = 0, p(0) = 0 and
p(η) → 1 as η → ∞, with no bound assumed on p, has wall shear q(0) = f''(0) strictly between
1.2325876568 and 1.2325876569. -/
theorem hiemenz_limit_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)) :
    1.2325876568 < q 0 ∧ q 0 < 1.2325876569 := by
  sorry

/-- Hiemenz stagnation-point flow: for every solution (f, p, q) and every solution (f₂, p₂, q₂) of
f''' + f f'' + 1 − f'² = 0 on [0, ∞) (derivatives one-sided at 0), both with f(0) = 0, p(0) = 0 and
p(η) → 1 as η → ∞, with no bound assumed on p: f η = f₂ η, p η = p₂ η and q η = q₂ η for every
η ≥ 0. -/
theorem hiemenz_limit_equal (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - 1 + p₂ η ^ 2) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1)) :
    ∀ η ∈ Ici (0 : ℝ), f η = f₂ η ∧ p η = p₂ η ∧ q η = q₂ η := by
  sorry

/-- Homann axisymmetric stagnation-point flow: every solution of f''' + 2 f f'' + 1 − f'² = 0 on [0, ∞) (f has derivative p, p has
derivative q, q has derivative −2 f q − 1 + p², one-sided at 0) with f(0) = 0, p(0) = 0 and
p(η) → 1 as η → ∞, with no bound assumed on p, has wall shear q(0) = f''(0) strictly between
1.3119376938 and 1.3119376939. -/
theorem homann_limit_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(2 * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)) :
    1.3119376938 < q 0 ∧ q 0 < 1.3119376939 := by
  sorry

/-- Homann axisymmetric stagnation-point flow: for every solution (f, p, q) and every solution (f₂, p₂, q₂) of
f''' + 2 f f'' + 1 − f'² = 0 on [0, ∞) (derivatives one-sided at 0), both with f(0) = 0, p(0) = 0 and
p(η) → 1 as η → ∞, with no bound assumed on p: f η = f₂ η, p η = p₂ η and q η = q₂ η for every
η ≥ 0. -/
theorem homann_limit_equal (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(2 * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(2 * f₂ η * q₂ η) - 1 + p₂ η ^ 2) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1)) :
    ∀ η ∈ Ici (0 : ℝ), f η = f₂ η ∧ p η = p₂ η ∧ q η = q₂ η := by
  sorry

/-- Falkner–Skan β = 1/2: every solution of f''' + f f'' + (1 − f'²)/2 = 0 on [0, ∞) (f has derivative p, p has
derivative q, q has derivative −f q − (1 − p²)/2, one-sided at 0) with f(0) = 0, p(0) = 0 and
p(η) → 1 as η → ∞, with no bound assumed on p, has wall shear q(0) = f''(0) strictly between
0.927680039 and 0.927680040. -/
theorem fs_half_limit_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 2 * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)) :
    0.927680039 < q 0 ∧ q 0 < 0.927680040 := by
  sorry

/-- Falkner–Skan β = 1/2: for every solution (f, p, q) and every solution (f₂, p₂, q₂) of
f''' + f f'' + (1 − f'²)/2 = 0 on [0, ∞) (derivatives one-sided at 0), both with f(0) = 0, p(0) = 0 and
p(η) → 1 as η → ∞, with no bound assumed on p: f η = f₂ η, p η = p₂ η and q η = q₂ η for every
η ≥ 0. -/
theorem fs_half_limit_equal (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 2 * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - 1 / 2 * (1 - p₂ η ^ 2)) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1)) :
    ∀ η ∈ Ici (0 : ℝ), f η = f₂ η ∧ p η = p₂ η ∧ q η = q₂ η := by
  sorry

/-- Falkner–Skan β = 1/5: every solution of f''' + f f'' + (1 − f'²)/5 = 0 on [0, ∞) (f has derivative p, p has
derivative q, q has derivative −f q − (1 − p²)/5, one-sided at 0) with f(0) = 0, p(0) = 0 and
p(η) → 1 as η → ∞, with no bound assumed on p, has wall shear q(0) = f''(0) strictly between
0.6867081809 and 0.6867081811. -/
theorem fs_fifth_limit_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 5 * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)) :
    0.6867081809 < q 0 ∧ q 0 < 0.6867081811 := by
  sorry

/-- Falkner–Skan β = 1/5: for every solution (f, p, q) and every solution (f₂, p₂, q₂) of
f''' + f f'' + (1 − f'²)/5 = 0 on [0, ∞) (derivatives one-sided at 0), both with f(0) = 0, p(0) = 0 and
p(η) → 1 as η → ∞, with no bound assumed on p: f η = f₂ η, p η = p₂ η and q η = q₂ η for every
η ≥ 0. -/
theorem fs_fifth_limit_equal (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 5 * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - 1 / 5 * (1 - p₂ η ^ 2)) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1)) :
    ∀ η ∈ Ici (0 : ℝ), f η = f₂ η ∧ p η = p₂ η ∧ q η = q₂ η := by
  sorry

end Work.FalknerSkan.Unrestricted
