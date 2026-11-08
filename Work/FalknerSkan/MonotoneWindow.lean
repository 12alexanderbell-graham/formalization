import Mathlib

/-!
# Wall shear of every monotone solution: Hiemenz and Homann stagnation-point flows

Frozen statements (run 2026-11-08T1028Z), before any proof.

Hiemenz (plane) stagnation-point flow: f''' + f f'' + 1 − f'² = 0; Homann (axisymmetric)
stagnation-point flow: f''' + 2 f f'' + 1 − f'² = 0; both with f(0) = f'(0) = 0 and f'(η) → 1 as
η → ∞. Written as the first-order system f' = p, p' = q, q' = −k f q − 1 + p² (k = 1 Hiemenz,
k = 2 Homann), derivatives within [0, ∞) (one-sided at 0).

The headlines say: **every** solution of the boundary-value problem whose velocity profile is
strictly increasing in the strong sense f'' > 0 on [0, ∞) (the class in which Coppel 1960 proved
uniqueness for Falkner–Skan β ≥ 0) has its wall shear f''(0) in the window whose two ends are the
shooting values of `Checked.Hiemenz.hiemenz_under`/`hiemenz_over` (resp.
`Checked.Homann.homann_under`/`homann_over`). With `hiemenz_exists`/`homann_exists` this places
the wall shear of the physical (monotone) solution, not merely of some solution.

Planned proof (no new numerical certificate): Crocco variables t = f'(η), z(t) = f''(η),
F(t) = f(η) turn the system into dF/dt = t/z, dz/dt = −k F − (1 − t²)/z on the range of f'.
For two solutions with z₂(0) > z₁(0) the differences D = z₂ − z₁, E = F₂ − F₁ satisfy
E' = −t D/(z₁ z₂), D' = −k E + (1 − t²) D/(z₁ z₂), a cooperative linear system started at
(D, E) = (D(0), 0), so D ≥ D(0) on the common range. Comparing the boundary-value solution with
the certified overshoot (resp. undershoot) solution at the window's ends then contradicts
z → 0 at the end of its range.
-/

namespace Work.FalknerSkan.MonotoneWindow
open Set Filter Topology

/-- Hiemenz stagnation-point flow: every solution of f''' + f f'' + 1 − f'² = 0 on [0, ∞)
(f has derivative p, p has derivative q, q has derivative −f q − 1 + p², one-sided at 0) with
f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞ and q > 0 on [0, ∞) has wall shear q(0) = f''(0)
strictly between 1.2325876568 and 1.2325876569. -/
theorem hiemenz_monotone_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η) :
    1.2325876568 < q 0 ∧ q 0 < 1.2325876569 := by
  sorry

/-- Homann axisymmetric stagnation-point flow: every solution of f''' + 2 f f'' + 1 − f'² = 0 on
[0, ∞) (f has derivative p, p has derivative q, q has derivative −2 f q − 1 + p², one-sided at 0)
with f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞ and q > 0 on [0, ∞) has wall shear q(0) = f''(0)
strictly between 1.3119376938 and 1.3119376939. -/
theorem homann_monotone_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(2 * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η) :
    1.3119376938 < q 0 ∧ q 0 < 1.3119376939 := by
  sorry

end Work.FalknerSkan.MonotoneWindow
