import Mathlib

namespace Blind.TownesExists

/-- `θ : ℝ → ℝ` is a positive decaying radial profile for `ΔQ - Q + Q³ = 0` in `ℝ²`,
`Q(x) = θ(‖x‖)`.  Choices: `θ` is `C²` on all of `ℝ` (so the radial function is `C²` at the
origin, with the even extension understood), `θ'(0) = 0`, the radial ODE holds for `r > 0`,
`θ > 0` on `[0,∞)`, and `θ(r) → 0` as `r → ∞`. -/
def IsRadialProfile (θ : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 θ ∧
  deriv θ 0 = 0 ∧
  (∀ r : ℝ, 0 < r →
    deriv (deriv θ) r + (1 / r) * deriv θ r - θ r + (θ r) ^ 3 = 0) ∧
  (∀ r : ℝ, 0 ≤ r → 0 < θ r) ∧
  Filter.Tendsto θ Filter.atTop (nhds 0)

/-- There is a ground state whose central value lies in `(2.2062008646, 2.2062008647)`. -/
theorem ground_state_exists :
    ∃ θ : ℝ → ℝ, IsRadialProfile θ ∧
      (2.2062008646 : ℝ) < θ 0 ∧ θ 0 < (2.2062008647 : ℝ) := by
  sorry

end Blind.TownesExists
