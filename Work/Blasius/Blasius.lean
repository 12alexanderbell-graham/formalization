import Mathlib

/-!
# Fluid mechanics (THE RESULT parts 2 and 5): the wall shear constant of the Blasius boundary
# layer (frozen before proof, run 2026-11-07T1228Z)

**Question.** The steady laminar boundary layer on a flat plate in a uniform stream (Blasius
1908) reduces, in the similarity variable η, to
  f''' + f f''/2 = 0 on [0, ∞),  f(0) = f'(0) = 0,  f'(η) → 1 as η → ∞,
where f' is the streamwise velocity profile. The wall shear (skin friction) is proportional to
σ = f''(0). Floating-point values of σ are printed to many digits (Boyd 1999: 0.33205733621519630);
the prior-art screen of this run (`runs/2026-11-07T1228Z/prior_art_blasius.md`) found one rigorous
enclosure, 0.3320574 ± 0.000016 (Costin and Tanveer, arXiv:1303.1416), about five digits, and no
machine-checked result.

**What is stated here.** For every solution (f with derivative p, p with derivative q, q with
derivative −f q/2 on [0, ∞), one-sided at 0) with f(0) = p(0) = 0 and p(η) → 1, the wall shear
q(0) lies in [0.33205733621519, 0.33205733621520]. Existence of a solution is stated separately
(`Work/Blasius/BlasiusExists.lean`).

Only Mathlib definitions occur in the statement.
-/

namespace Work.Blasius
open Set Filter Topology

/-- Blasius boundary layer, wall shear: for every solution f of f''' + f f''/2 = 0 on [0, ∞)
(f has derivative p, p has derivative q, q has derivative −f q/2, one-sided at 0) with
f(0) = 0, p(0) = 0 and p(η) → 1 as η → ∞, the wall value q(0) = f''(0) lies between
0.33205733621519 and 0.33205733621520. -/
theorem blasius_wall_shear (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η / 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)) :
    0.33205733621519 ≤ q 0 ∧ q 0 ≤ 0.33205733621520 := by
  sorry

end Work.Blasius
