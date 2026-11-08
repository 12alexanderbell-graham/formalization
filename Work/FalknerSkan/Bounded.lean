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
* `hiemenz_bounded_equal`, `homann_bounded_equal`: any two such solutions are equal on [0, ∞).
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
  have hq1 : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(1 * f η * q η) - 1 + p η ^ 2) (Ici 0) η :=
    fun η hη => (hq η hη).congr_deriv (by ring)
  exact Checked.FalknerSkan.MonotoneWindow.hiemenz_monotone_window f p q hf hp hq hf0 hp0 hlim
    (Work.FalknerSkan.BoundedTools.pos_of_abs_le hf hp hq1 hp0 hlim hb)

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
  exact Checked.FalknerSkan.MonotoneWindow.homann_monotone_window f p q hf hp hq hf0 hp0 hlim
    (Work.FalknerSkan.BoundedTools.pos_of_abs_le hf hp hq hp0 hlim hb)

/-- Hiemenz stagnation-point flow: for every solution (f, p, q) and every solution (f₂, p₂, q₂) of f''' + f f'' + 1 − f'² = 0
on [0, ∞) (derivatives one-sided at 0), both with f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞ and
−1 ≤ p ≤ 1 on [0, ∞): f η = f₂ η, p η = p₂ η and q η = q₂ η for every η ≥ 0. -/
theorem hiemenz_bounded_equal (f p q f₂ p₂ q₂ : ℝ → ℝ)
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
  have hq1 : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(1 * f η * q η) - 1 + p η ^ 2) (Ici 0) η :=
    fun η hη => (hq η hη).congr_deriv (by ring)
  have hq₂1 : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(1 * f₂ η * q₂ η) - 1 + p₂ η ^ 2) (Ici 0) η :=
    fun η hη => (hq₂ η hη).congr_deriv (by ring)
  have hpos := Work.FalknerSkan.BoundedTools.pos_of_abs_le hf hp hq1 hp0 hlim hb
  have hpos₂ := Work.FalknerSkan.BoundedTools.pos_of_abs_le hf₂ hp₂ hq₂1 hp₂0 hlim₂ hb₂
  have hw : q 0 = q₂ 0 := le_antisymm
    (not_lt.1 (Checked.FalknerSkan.MonotoneExists.not_lt_wall zero_le_one hf₂ hp₂ hq₂1 hf₂0 hp₂0
      hlim₂ hpos₂ hf hp hq1 hf0 hp0 hlim hpos))
    (not_lt.1 (Checked.FalknerSkan.MonotoneExists.not_lt_wall zero_le_one hf hp hq1 hf0 hp0 hlim
      hpos hf₂ hp₂ hq₂1 hf₂0 hp₂0 hlim₂ hpos₂))
  exact Work.FalknerSkan.BoundedTools.eq_of_start hf hp hq1 hf₂ hp₂ hq₂1 (hf0.trans hf₂0.symm) (hp0.trans hp₂0.symm) hw

/-- Homann axisymmetric stagnation-point flow: for every solution (f, p, q) and every solution (f₂, p₂, q₂) of f''' + 2 f f'' + 1 − f'² = 0
on [0, ∞) (derivatives one-sided at 0), both with f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞ and
−1 ≤ p ≤ 1 on [0, ∞): f η = f₂ η, p η = p₂ η and q η = q₂ η for every η ≥ 0. -/
theorem homann_bounded_equal (f p q f₂ p₂ q₂ : ℝ → ℝ)
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
  have hpos := Work.FalknerSkan.BoundedTools.pos_of_abs_le hf hp hq hp0 hlim hb
  have hpos₂ := Work.FalknerSkan.BoundedTools.pos_of_abs_le hf₂ hp₂ hq₂ hp₂0 hlim₂ hb₂
  have hw : q 0 = q₂ 0 := le_antisymm
    (not_lt.1 (Checked.FalknerSkan.MonotoneExists.not_lt_wall zero_le_two hf₂ hp₂ hq₂ hf₂0 hp₂0
      hlim₂ hpos₂ hf hp hq hf0 hp0 hlim hpos))
    (not_lt.1 (Checked.FalknerSkan.MonotoneExists.not_lt_wall zero_le_two hf hp hq hf0 hp0 hlim
      hpos hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hpos₂))
  exact Work.FalknerSkan.BoundedTools.eq_of_start hf hp hq hf₂ hp₂ hq₂ (hf0.trans hf₂0.symm) (hp0.trans hp₂0.symm) hw

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
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hpos, hlo, hhi⟩ :=
    Checked.FalknerSkan.MonotoneExists.hiemenz_exists_monotone
  exact ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, Work.FalknerSkan.BoundedTools.bounded_of_pos hp hp0 hlim hpos, hlo, hhi⟩

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
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hpos, hlo, hhi⟩ :=
    Checked.FalknerSkan.MonotoneExists.homann_exists_monotone
  exact ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, Work.FalknerSkan.BoundedTools.bounded_of_pos hp hp0 hlim hpos, hlo, hhi⟩

end Work.FalknerSkan.Bounded
