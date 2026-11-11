import Mathlib
import Work.FSSep.SBase

/-!
# Falkner–Skan separation: the pressure-gradient parameter of the zero-wall-shear profile

Frozen in run 2026-11-11T0232Z (statement first, proof follows). Program β-form:
f' = p, p' = q, q' = −f q − β (1 − p²), one-sided derivatives at 0, f(0) = 0, p(0) = 0, and the
separation condition q(0) = f''(0) = 0. The solution sought tends to the outer flow (p → 1) in the
decay class of the attached Falkner–Skan solutions (for every M, eventually M (1 − p) ≤ q): for
β* < β < 0 the zero-shear shot also reaches p → 1, but only with an algebraic tail, outside this
class (`runs/2026-11-09T0428Z/research/fs_negative_beta.md` §1.4–1.5).
Plan: shoot K = 1/(−β) from (0, 0, 0) in the scaled field `Work.FSSep.SBase.vS`; certified
Over at K = 10¹⁰/1988377351 and SlowS at K = 10¹⁰/1988377350; a neither-point by the supremum
argument of `Work.FSNeg.NAssemble.core_exists`, with continuity of the flow in K.
-/

namespace Work.FalknerSkan.Separation

open Set Filter Topology

/-- Falkner–Skan separation: there is β with −0.1988377351 < β < −0.1988377350 and a solution
(f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with f(0) = 0, p(0) = 0, zero wall shear
q(0) = 0, p → 1, q > 0 on (0, ∞) and, for every M, eventually M (1 − p) ≤ q. -/
theorem fs_separation_exists :
    ∃ β ∈ Ioo (-(1988377351 / 10000000000 : ℝ)) (-(1988377350 / 10000000000)),
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ q 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ioi (0 : ℝ), 0 < q η) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) := by
  sorry

end Work.FalknerSkan.Separation
