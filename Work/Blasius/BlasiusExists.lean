import Mathlib

/-!
# Fluid mechanics: existence of a Blasius boundary layer (frozen before proof, run 2026-11-07T1228Z)

Companion of `Work/Blasius/Blasius.lean`: there is a solution f of f''' + f f''/2 = 0 on [0, ∞)
(f has derivative p, p has derivative q, q has derivative −f q/2, one-sided at 0) with
f(0) = p(0) = 0 and p(η) → 1 (classical: Töpfer 1912, Weyl 1942). Together with the wall-shear
theorem it shows that the bound there is not vacuous.

Only Mathlib definitions occur in the statement.
-/

namespace Work.Blasius
open Set Filter Topology

/-- Blasius boundary layer, existence: there are functions f, p, q on the reals such that f has
derivative p, p has derivative q and q has derivative −f q/2 on [0, ∞) (one-sided at 0), with
f(0) = 0, p(0) = 0 and p(η) → 1 as η → ∞. -/
theorem blasius_exists : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η / 2)) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) := by
  sorry

end Work.Blasius
