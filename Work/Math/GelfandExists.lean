import Mathlib

/-!
# Gelfand problem in the 3-D ball: existence of a solution meeting every hypothesis of the
# headline `Work.Math.Gelfand.gelfand_ball_critical`

Frozen before proof (annex 40.1), run 2026-11-06T1228Z. For every S ≥ 1/2 there are w, φ with
w differentiable within [0, S] with derivative φ, φ continuous at 0, φ' = −(2/s)φ − e^w on (0, S]
and w(0) = 0 (the regular solution of the isothermal Emden–Chandrasekhar equation exists on
[0, S]). Planned route: the Lane–Emden existence route (`Work/Math/LEExists*.lean`) with θ³
replaced by a clamped exponential; on [1/2, S] the clamps stay inactive because s²φ is
decreasing (so w ≤ 0) and bounded below.
-/

namespace Work.Math.GelfandExists
open Set

/-- For every S ≥ 1/2 there exist w, φ with w differentiable within [0, S] with derivative φ, φ
continuous at 0, φ' = −(2/s)φ − e^w on (0, S] and w(0) = 0: the hypotheses of the Gelfand
headline are satisfied together. -/
theorem exists_solution (S : ℝ) (hS : 1 / 2 ≤ S) : ∃ w φ : ℝ → ℝ,
    (∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s) ∧
    ContinuousWithinAt φ (Icc 0 S) 0 ∧
    (∀ s ∈ Ioc (0 : ℝ) S, HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s) ∧
    w 0 = 0 := by
  sorry

end Work.Math.GelfandExists
