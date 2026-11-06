import Mathlib

/-!
# Mathematics (THE RESULT part 5): the critical parameter of the Gelfand problem in the
# three-dimensional ball, certified

**Question.** The Gelfand (Frank-Kamenetskii thermal-explosion) problem Δu + λ eᵘ = 0 in the
unit ball of ℝ³, u = 0 on the boundary, has solutions exactly for λ up to a critical value λ*.
Its radial solutions are u(r) = w(s r) − w(s), λ = s² e^{w(s)} (s > 0), where w is the solution
of the isothermal Emden–Chandrasekhar equation
  w'' + (2/s) w' + eʷ = 0,  w(0) = 0,
regular at the singular point s = 0. So λ* is the maximum over s of Λ(s) = s² e^{w(s)}. The
values in the literature found by the screen of run 2026-11-06T1028Z (Frank-Kamenetskii's
sphere value, the combustion literature) come from floating-point computation; the screen found
no rigorous enclosure, and no proof that the first local maximum of Λ is its global maximum
on a stated interval with certified digits.

**What is stated here** (frozen before proof, annex 40.1). For every S ≥ 41/10 and every w on
[0, S] that is differentiable on [0, S] with derivative φ (one-sided at the ends), with φ
continuous at 0, φ differentiable on (0, S] with φ' = −(2/s)φ − e^{w}, and w(0) = 0: there is a
point s₁ with 4.071496844 ≤ s₁ ≤ 4.071496845 at which s² e^{w(s)} attains its maximum over the
whole interval [0, S], and that maximum lies between 3.321992118 and 3.321992119.
w'(0) = 0 is not assumed (it follows from boundedness at the singular point). Existence of such
a w is a separate statement (not yet stated).

Only Mathlib definitions occur in the statement (no program definition to pin).
-/

namespace Work.Math.Gelfand
open Set

/-- Gelfand problem in the three-dimensional ball, radial branch: for every S ≥ 41/10 and every
solution w of w'' + (2/s)w' + e^w = 0 on (0, S] with w(0) = 0, w differentiable on [0, S] with
derivative φ and φ continuous at 0, the function s² e^{w(s)} attains its maximum over [0, S] at a
point s₁ between 4.071496844 and 4.071496845, and the maximum value lies between 3.321992118 and
3.321992119. -/
theorem gelfand_ball_critical (S : ℝ) (hS : 41 / 10 ≤ S) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    (h0 : w 0 = 0) :
    ∃ s₁ : ℝ, 4.071496844 ≤ s₁ ∧ s₁ ≤ 4.071496845 ∧
      (∀ s ∈ Icc 0 S, s ^ 2 * Real.exp (w s) ≤ s₁ ^ 2 * Real.exp (w s₁)) ∧
      3.321992118 ≤ s₁ ^ 2 * Real.exp (w s₁) ∧ s₁ ^ 2 * Real.exp (w s₁) ≤ 3.321992119 := by
  sorry

end Work.Math.Gelfand
