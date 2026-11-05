import Mathlib

/-!
# Lane–Emden n = 3, blind restatement

Reading choices.
* `θ : ℝ → ℝ`; only its values on `[0, 7]` matter.
* Regularity: `θ` continuous on `[0,7]`; `θ 0 = 1`; `θ` has one-sided derivative `0`
  at `0` (`HasDerivWithinAt θ 0 (Ici 0) 0`). The singular point is not otherwise used in the ODE.
* ODE on the open interval `(0,7)` in divergence form
  `(ξ² θ')' = -ξ² θ³` (equivalent to `θ'' + (2/ξ)θ' = -θ³` for `ξ ≠ 0`), with `θ`
  differentiable at each such `ξ` and `ξ ↦ ξ² · deriv θ ξ` having that derivative there.
  No derivative is demanded at `7`.
* "First zero": `θ ξ₁ = 0` and `θ > 0` on `[0, ξ₁)`. Since `ξ₁ < 7`, `ξ₁` is interior and
  `deriv θ ξ₁` is the genuine two-sided derivative.
* `ω₃ = -ξ₁² θ'(ξ₁)`, `ρ_c/ρ̄ = ξ₁³/(3 ω₃)`; claimed bounds are the stated closed intervals.
  Ambiguity: source prints rounded values; we require only the sharper claimed intervals.
-/

namespace Work.Math.LaneEmdenBlind

theorem blind_laneEmden3 (θ : ℝ → ℝ)
    (hcont : ContinuousOn θ (Set.Icc 0 7))
    (h0 : θ 0 = 1)
    (hd0 : HasDerivWithinAt θ 0 (Set.Ici 0) 0)
    (hode : ∀ ξ ∈ Set.Ioo (0:ℝ) 7, DifferentiableAt ℝ θ ξ ∧
      HasDerivAt (fun x => x ^ 2 * deriv θ x) (-(ξ ^ 2 * θ ξ ^ 3)) ξ) :
    ∃ ξ₁ : ℝ, ξ₁ ∈ Set.Ioo (0:ℝ) 7 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Set.Ico 0 ξ₁, 0 < θ ξ) ∧
      ξ₁ ∈ Set.Icc (6.896848615 : ℝ) 6.896848625 ∧
      (-(ξ₁ ^ 2 * deriv θ ξ₁)) ∈ Set.Icc (2.018235945 : ℝ) 2.018235955 ∧
      (ξ₁ ^ 3 / (3 * (-(ξ₁ ^ 2 * deriv θ ξ₁)))) ∈ Set.Icc (54.1824805 : ℝ) 54.1824815 := by
  sorry

end Work.Math.LaneEmdenBlind
