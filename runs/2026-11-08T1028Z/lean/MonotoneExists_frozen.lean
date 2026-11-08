import Mathlib

/-!
# The monotone solution: existence and one wall shear (Hiemenz, Homann)

Frozen statements (run 2026-11-08T1028Z), before any proof; companions of
`Work.FalknerSkan.MonotoneWindow`. Hiemenz: f''' + f f'' + 1 − f'² = 0; Homann:
f''' + 2 f f'' + 1 − f'² = 0; f(0) = f'(0) = 0, f'(η) → 1 as η → ∞; first-order system
f' = p, p' = q with derivatives within [0, ∞).

* `hiemenz_exists_monotone`, `homann_exists_monotone`: there is a solution with q = f'' > 0 on
  [0, ∞) and wall shear in the certified window (the existence theorems `hiemenz_exists`,
  `homann_exists` do not say q > 0).
* `hiemenz_monotone_same_wall_shear`, `homann_monotone_same_wall_shear`: any two solutions with
  q > 0 on [0, ∞) have the same wall shear q(0).

Planned proofs: the shooting construction of `Checked.Hiemenz.HExAssemble.exists_bvp` (resp. the
Homann copy) already proves q > 0 inside `HExLimit.no_event`; expose it. Same wall shear: the
Crocco comparison of `Work.FalknerSkan.CroccoWindow` between the two solutions.
-/

namespace Work.FalknerSkan.MonotoneExists
open Set Filter Topology

/-- Hiemenz stagnation-point flow: there is a solution of f''' + f f'' + 1 − f'² = 0 on [0, ∞)
(f has derivative p, p has derivative q, q has derivative −f q − 1 + p², one-sided at 0) with
f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞, q > 0 on [0, ∞), and wall shear q(0) = f''(0) strictly
between 1.2325876568 and 1.2325876569. -/
theorem hiemenz_exists_monotone : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧ (∀ η ∈ Ici (0 : ℝ), 0 < q η) ∧
    1.2325876568 < q 0 ∧ q 0 < 1.2325876569 := by
  sorry

/-- Homann axisymmetric stagnation-point flow: there is a solution of f''' + 2 f f'' + 1 − f'² = 0
on [0, ∞) (f has derivative p, p has derivative q, q has derivative −2 f q − 1 + p², one-sided at
0) with f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞, q > 0 on [0, ∞), and wall shear q(0) = f''(0)
strictly between 1.3119376938 and 1.3119376939. -/
theorem homann_exists_monotone : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(2 * f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧ (∀ η ∈ Ici (0 : ℝ), 0 < q η) ∧
    1.3119376938 < q 0 ∧ q 0 < 1.3119376939 := by
  sorry

/-- Hiemenz stagnation-point flow: any two solutions of f''' + f f'' + 1 − f'² = 0 on [0, ∞)
(derivatives one-sided at 0) with f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞ and q > 0 on [0, ∞) have
the same wall shear q(0) = f''(0). -/
theorem hiemenz_monotone_same_wall_shear (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - 1 + p₂ η ^ 2) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1))
    (hpos₂ : ∀ η ∈ Ici (0 : ℝ), 0 < q₂ η) :
    q 0 = q₂ 0 := by
  sorry

/-- Homann axisymmetric stagnation-point flow: any two solutions of f''' + 2 f f'' + 1 − f'² = 0
on [0, ∞) (derivatives one-sided at 0) with f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞ and q > 0 on
[0, ∞) have the same wall shear q(0) = f''(0). -/
theorem homann_monotone_same_wall_shear (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(2 * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(2 * f₂ η * q₂ η) - 1 + p₂ η ^ 2) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1))
    (hpos₂ : ∀ η ∈ Ici (0 : ℝ), 0 < q₂ η) :
    q 0 = q₂ 0 := by
  sorry

end Work.FalknerSkan.MonotoneExists
