import Mathlib
import Checked.Homann.Homann
import Checked.Blasius.Blasius

/-!
# Fluid mechanics (THE RESULT parts 2 and 1): two rows of the Falkner–Skan wall-shear table from
# the certified Homann and Blasius results (frozen before proof, run 2026-11-08T0828Z)

**Question.** The Falkner–Skan boundary-value problem
  g''' + g g'' + β (1 − g'²) = 0,  g(0) = g'(0) = 0,  g'(η) → 1 as η → ∞,
has a classical table of wall shears g''(0) against β (Hartree 1937; modern tables print six
digits: 0.469600 at β = 0, 0.927680 at β = 1/2, 1.232588 at β = 1). The similarity scaling
F(s) = c f(s/c) maps solutions of f''' + a f f'' + b (1 − f'²) = 0 to solutions of
F''' + (a/c²) F F'' + (b/c²)(1 − F'²) = 0 and divides the wall shear by c. With c = √2 the
Homann problem (a = 2, b = 1) becomes β = 1/2 and the Blasius problem in the form
f''' + f f''/2 = 0 becomes β = 0. The Hiemenz problem is β = 1 as it stands.

**Statements.** Writing p = g' and q = g'' (derivatives within [0, ∞), one-sided at 0):
* `fs_half_exists`: there is a solution of the β = 1/2 problem with q(0) strictly between
  0.927680039 and 0.927680040.
* `fs_zero_wall_shear`: every solution of the β = 0 problem has q(0) between 0.4695999883610
  and 0.4695999883611.

Uniqueness of the β = 1/2 solution is not part of these statements.
-/

namespace Work.FalknerSkan
open Set Filter Topology

/-- Falkner–Skan β = 1/2, existence: there is a solution of g''' + g g'' + (1 − g'²)/2 = 0 on
[0, ∞) (g has derivative p, p has derivative q, q has derivative −g q − (1 − p²)/2, one-sided
at 0) with g(0) = 0, p(0) = 0 and p(η) → 1 as η → ∞ whose wall value q(0) = g''(0) lies
strictly between 0.927680039 and 0.927680040. -/
theorem fs_half_exists : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 2 * (1 - p η ^ 2)) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    0.927680039 < q 0 ∧ q 0 < 0.927680040 := by
  sorry

/-- Falkner–Skan β = 0, wall shear: for every solution of g''' + g g'' = 0 on [0, ∞) (g has
derivative p, p has derivative q, q has derivative −g q, one-sided at 0) with g(0) = 0,
p(0) = 0 and p(η) → 1 as η → ∞, the wall value q(0) = g''(0) lies between 0.4695999883610
and 0.4695999883611. -/
theorem fs_zero_wall_shear (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)) :
    0.4695999883610 ≤ q 0 ∧ q 0 ≤ 0.4695999883611 := by
  sorry

end Work.FalknerSkan
