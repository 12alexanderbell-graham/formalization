import Mathlib

namespace Blind.Townes

/-!
# Townes soliton shooting claims

Modelling choices:
* A solution is a pair of functions `θ θ' : ℝ → ℝ` (value and derivative); only values on
  `[0, 13.6]` matter.
* Interval: `R = 13.6`.
* ODE: for every `r ∈ (0, 13.6)`, `HasDerivAt θ (θ' r) r` and
  `HasDerivAt θ' (θ r - θ r ^ 3 - θ' r / r) r`, i.e. `θ'' + θ'/r - θ + θ^3 = 0`.
  (Open interval: avoids one-sided derivative issues at the endpoints; the endpoint 13.6 is
  covered by continuity.)
* Regularity at 0: `θ` and `θ'` are continuous on `[0, 13.6]` (so continuous at 0 from the
  right) and `θ' 0 = 0`. No uniqueness is assumed.
* Initial value `θ 0` is the literal decimal.
* Claim (A) conclusion: exists `0 < r ≤ 13.6` with `θ' r > 0` and `θ > 0` on `[0, r]`.
* Claim (B) conclusion: exists `0 < r ≤ 13.6` with `θ r < 0` and `θ' < 0` on `(0, r]`.
-/

/-- `θ` (with derivative `θ'`) solves the radial Townes IVP on `[0, 13.6]` with `θ 0 = a`. -/
def IsSolution (a : ℝ) (θ θ' : ℝ → ℝ) : Prop :=
  (∀ r ∈ Set.Ioo (0 : ℝ) 13.6, HasDerivAt θ (θ' r) r) ∧
  (∀ r ∈ Set.Ioo (0 : ℝ) 13.6, HasDerivAt θ' (θ r - θ r ^ 3 - θ' r / r) r) ∧
  ContinuousOn θ (Set.Icc 0 13.6) ∧
  ContinuousOn θ' (Set.Icc 0 13.6) ∧
  θ' 0 = 0 ∧ θ 0 = a

/-- Undershoot: for `θ(0) = 2.2062008646`, every solution has, at some `0 < r ≤ 13.6`,
strictly positive derivative while `θ` is strictly positive on all of `[0, r]`. -/
theorem under (θ θ' : ℝ → ℝ) (h : IsSolution 2.2062008646 θ θ') :
    ∃ r : ℝ, 0 < r ∧ r ≤ 13.6 ∧ 0 < θ' r ∧ ∀ s ∈ Set.Icc (0 : ℝ) r, 0 < θ s := by
  sorry

/-- Overshoot: for `θ(0) = 2.2062008647`, every solution becomes strictly negative at some
`0 < r ≤ 13.6`, with derivative strictly negative on all of `(0, r]`. -/
theorem «over» (θ θ' : ℝ → ℝ) (h : IsSolution 2.2062008647 θ θ') :
    ∃ r : ℝ, 0 < r ∧ r ≤ 13.6 ∧ θ r < 0 ∧ ∀ s ∈ Set.Ioc (0 : ℝ) r, θ' s < 0 := by
  sorry

end Blind.Townes
