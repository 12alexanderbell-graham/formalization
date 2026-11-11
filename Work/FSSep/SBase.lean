import Mathlib
import Work.FSNeg.NBase

/-!
# Falkner–Skan separation (zero wall shear), scaled form: the clamped field with a free
# coefficient K and the two shooting events (run 2026-11-11T0232Z)

Scaling F(s) = c f(s/c), c = √(−β), turns f''' + f f'' + β(1 − f'²) = 0 (β < 0) into
F''' + K F F'' − (1 − F'²) = 0 with K = 1/(−β) (`Checked.FalknerSkan.FSScale.scale`); the wall
shear F''(0) = f''(0)/c is zero exactly when f''(0) is. The separation problem shoots the
coefficient K from the fixed start (0, 0, 0).

`vS K t y` is the field (p, q, −K f q + 1 − p²) for y = (f, p, q) with p and q clamped to [−2, 2]
and f to [−(t⁺ + 2), t⁺ + 2], as `Work.FSNeg.NBase.vN` with 10 replaced by K.
`Over` (from `NBase`): p > 1 somewhere. `SlowS Y`: at some η > 0, 0 ≤ p < 1, q < 3(1 − p) and
f > 11/15, with p < 1 on [0, η] (no sign condition on q along the path: q(0) = 0 here; q > 0 on
(0, η] follows from the equation). With μ = 3 and θ = 11/15, μ + 2/μ ≤ K θ for every K ≥ 5, so the
region is forward invariant (`Work.FSNeg.NSlowInv.slow_inv`).
-/

namespace Work.FSSep.SBase
open Set Work.FSNeg.NBase

/-- The clamped coefficient-K field with the adverse pressure sign. -/
noncomputable def vS (K t : ℝ) (y : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (cl 2 y.2.1, cl 2 y.2.2, -(K * cl (max t 0 + 2) y.1 * cl 2 y.2.2) + 1 - cl 2 y.2.1 ^ 2)

/-- Slow entry from a zero wall shear: at some η > 0 the trajectory is in the region 0 ≤ p < 1,
q < 3(1 − p), f > 11/15, having had p < 1 on [0, η]. -/
def SlowS (Y : ℝ → ℝ × ℝ × ℝ) : Prop :=
  ∃ η > 0, (∀ s ∈ Icc 0 η, (Y s).2.1 < 1) ∧
    0 ≤ (Y η).2.1 ∧ (Y η).2.2 < 3 * (1 - (Y η).2.1) ∧ 11 / 15 < (Y η).1

/-- The certified chain shape: every solution of the clamped coefficient-K field on [0, T] from
(0, 0, 0) has the event `E`. -/
def ChainK (K : ℝ) (E : (ℝ → ℝ × ℝ × ℝ) → Prop) : Prop :=
  ∃ T > 0, ∀ Y : ℝ → ℝ × ℝ × ℝ, (∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vS K t (Y t)) (Icc 0 T) t) →
    Y 0 = (0, 0, 0) → E Y

end Work.FSSep.SBase
