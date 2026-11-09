import Checked.FalknerSkan.TenthBounded
import Checked.FalknerSkan.Limit
/-! Falkner–Skan wedge flow with pressure-gradient coefficient one tenth, without any bound on the velocity profile: by the positivity of the second derivative for every solution of the boundary-value problem, the window and equality theorems of the class bounded by one in absolute value hold for every solution. Module `LimitTenth`. -/

namespace Checked.FalknerSkan.LimitTenth
open Set Filter Topology

/-- Falkner–Skan β = 1/10: every solution of f''' + f f'' + (1 − f'²)/10 = 0 on [0, ∞) (f has derivative p, p has
derivative q, q has derivative −f q − (1 − p²)/10, one-sided at 0) with f(0) = 0, p(0) = 0 and
p(η) → 1 as η → ∞ has wall shear q(0) = f''(0) strictly between
0.5870352191 and 0.5870352193. -/
theorem fs_tenth_limit_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 10 * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)) :
    0.5870352191 < q 0 ∧ q 0 < 0.5870352193 := by
  have hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1 := fun η hη => by
    have h := Checked.FalknerSkan.BoundedTools.bounded_of_pos hp hp0 hlim
      (Checked.FalknerSkan.Limit.fs_monotone_of_limit (1 / 10) (by norm_num) (by norm_num) f p q hf hp hq hf0 hp0 hlim) η hη
    exact ⟨by linarith [h.1], h.2.le⟩
  exact Checked.FalknerSkan.TenthBounded.fs_tenth_bounded_window f p q hf hp hq hf0 hp0 hlim hb

/-- Falkner–Skan β = 1/10: for every solution (f, p, q) and every solution (f₂, p₂, q₂) of
f''' + f f'' + (1 − f'²)/10 = 0 on [0, ∞) (derivatives one-sided at 0), both with f(0) = 0, p(0) = 0 and
p(η) → 1 as η → ∞: f η = f₂ η, p η = p₂ η and q η = q₂ η for every
η ≥ 0. -/
theorem fs_tenth_limit_equal (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 10 * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - 1 / 10 * (1 - p₂ η ^ 2)) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1)) :
    ∀ η ∈ Ici (0 : ℝ), f η = f₂ η ∧ p η = p₂ η ∧ q η = q₂ η := by
  have hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1 := fun η hη => by
    have h := Checked.FalknerSkan.BoundedTools.bounded_of_pos hp hp0 hlim
      (Checked.FalknerSkan.Limit.fs_monotone_of_limit (1 / 10) (by norm_num) (by norm_num) f p q hf hp hq hf0 hp0 hlim) η hη
    exact ⟨by linarith [h.1], h.2.le⟩
  have hb₂ : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p₂ η ∧ p₂ η ≤ 1 := fun η hη => by
    have h := Checked.FalknerSkan.BoundedTools.bounded_of_pos hp₂ hp₂0 hlim₂
      (Checked.FalknerSkan.Limit.fs_monotone_of_limit (1 / 10) (by norm_num) (by norm_num) f₂ p₂ q₂ hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂) η hη
    exact ⟨by linarith [h.1], h.2.le⟩
  exact Checked.FalknerSkan.TenthBounded.fs_tenth_bounded_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hb
    hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hb₂

end Checked.FalknerSkan.LimitTenth
