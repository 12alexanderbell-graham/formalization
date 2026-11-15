import Mathlib

/-! Blind restatement of `Work.Math.GelfandExtrema.gelfand_extrema` (run 2026-11-15T1228Z, Sonnet, brief `runs/2026-11-15T1228Z/blind/BRIEF.md`), copied verbatim from `runs/2026-11-15T1228Z/blind/GelfandExtremaBlind.lean` with a namespace added. -/

open Filter Set Real

namespace Work.Math.GelfandExtremaBlind

/-- The Gelfand–Bratu radial branch parameter attached to the regular solution `w`:
`λ(s) = s² e^{w(s)}`. -/
noncomputable def gelfandLambda (w : ℝ → ℝ) (s : ℝ) : ℝ := s ^ 2 * Real.exp (w s)

/-- `w` is the regular solution of `w'' + (2/s) w' + e^w = 0`, `w(0) = 0`, `w'(0) = 0`,
defined on `[0, ∞)`: `C²` up to `s = 0` (one-sided), with the ODE for `s > 0`. -/
structure IsRegularGelfandSolution (w : ℝ → ℝ) : Prop where
  contDiff : ContDiffOn ℝ 2 w (Ici (0 : ℝ))
  init_val : w 0 = 0
  init_deriv : derivWithin w (Ici (0 : ℝ)) 0 = 0
  ode : ∀ s : ℝ, 0 < s →
    deriv (deriv w) s + (2 / s) * deriv w s + Real.exp (w s) = 0

theorem blind_gelfand_extrema (w : ℝ → ℝ) (hw : IsRegularGelfandSolution w) :
    ∃ ζ : ℕ → ℝ,
      StrictMono ζ ∧ Tendsto ζ atTop atTop ∧
      (4.071496844 : ℝ) ≤ ζ 0 ∧ ζ 0 ≤ 4.071496845 ∧
      (3.321992118 : ℝ) ≤ gelfandLambda w (ζ 0) ∧
      gelfandLambda w (ζ 0) ≤ 3.321992119 ∧
      -- (i)
      (∀ s : ℝ, 0 ≤ s → s ≠ ζ 0 → gelfandLambda w s < gelfandLambda w (ζ 0)) ∧
      -- (ii)
      (∀ k : ℕ, ∀ s : ℝ, ζ (2 * k) ≤ s → s ≠ ζ (2 * k + 1) →
        gelfandLambda w (ζ (2 * k + 1)) < gelfandLambda w s) ∧
      -- (iii)
      (∀ k : ℕ, ∀ s : ℝ, ζ (2 * k + 1) ≤ s → s ≠ ζ (2 * k + 2) →
        gelfandLambda w s < gelfandLambda w (ζ (2 * k + 2))) ∧
      -- (iv)
      (∀ k : ℕ, gelfandLambda w (ζ (2 * k + 1)) < 2 ∧ 2 < gelfandLambda w (ζ (2 * k))) ∧
      -- (v)
      Tendsto (gelfandLambda w) atTop (nhds 2) ∧
      -- (vi)
      StrictMonoOn (gelfandLambda w) (Icc 0 (ζ 0)) ∧
      -- (vii)
      (∀ k : ℕ, StrictAntiOn (gelfandLambda w) (Icc (ζ (2 * k)) (ζ (2 * k + 1)))) ∧
      -- (viii)
      (∀ k : ℕ, StrictMonoOn (gelfandLambda w) (Icc (ζ (2 * k + 1)) (ζ (2 * k + 2)))) := by
  sorry

end Work.Math.GelfandExtremaBlind
