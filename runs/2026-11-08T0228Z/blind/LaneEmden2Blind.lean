import Mathlib

/-!
# Blind restatement: Lane-Emden n = 2

Reading choices:
* A solution is a pair of functions `θ θ' : ℝ → ℝ` (`θ'` is the derivative function, as data),
  with `HasDerivAt θ (θ' ξ) ξ` and `HasDerivAt θ' (-(2/ξ) * θ' ξ - θ ξ ^ 2) ξ` for every
  `ξ ∈ (0,5)` (open interior; ODE only needed away from the singular point ξ = 0).
* `θ²` is the literal square (no `|θ|^n` / positive-part truncation); the first zero
  is reached before θ becomes negative, so this is the same thing.
* Regularity at the centre: `θ` is continuous on `[0,5]`, `θ 0 = 1`, and
  `θ' ξ → 0` as `ξ → 0⁺` (this is the weakest form of "θ'(0) = 0"; no differentiability at
  0 is assumed separately). No uniqueness assumed.
* Endpoint ξ = 5: only continuity of `θ` there; `θ'` is not assumed to exist at 5, and the
  ODE is not required at 5 or at 0.
* "First zero": `ξ₁` is the least element of `{ξ ∈ [0,5] | θ ξ = 0}`; the theorem asserts
  existence of such ξ₁ (in particular a zero exists in [0,5]) and the bounds.
* ω₂ = -ξ₁² θ'(ξ₁) uses the supplied `θ' ξ₁`, which is the genuine derivative since
  ξ₁ ∈ (0,5) (ξ₁ ≠ 0 as θ 0 = 1; ξ₁ = 5 would be excluded by the conclusion's bound,
  but then `θ'` is unconstrained at 5 — so ξ₁ ∈ (0,5) is not asserted in the statement
  and is part of what must be proved).
* ρ_c/ρ̄ = ξ₁³/(3 ω₂), with real division.
* Bounds are the closed inequalities exactly as in the claim, with decimal literals.
-/

namespace Work.Math.LaneEmden2Blind

theorem blind_laneEmden2 (θ θ' : ℝ → ℝ)
    (hcont : ContinuousOn θ (Set.Icc 0 5))
    (h0 : θ 0 = 1)
    (hreg : Filter.Tendsto θ' (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hθ : ∀ ξ ∈ Set.Ioo (0:ℝ) 5, HasDerivAt θ (θ' ξ) ξ)
    (hθ' : ∀ ξ ∈ Set.Ioo (0:ℝ) 5,
      HasDerivAt θ' (-(2 / ξ) * θ' ξ - θ ξ ^ 2) ξ) :
    ∃ ξ₁ : ℝ, IsLeast {ξ : ℝ | ξ ∈ Set.Icc (0:ℝ) 5 ∧ θ ξ = 0} ξ₁ ∧
      (4.3528745959 ≤ ξ₁ ∧ ξ₁ ≤ 4.3528745960) ∧
      (2.4110460120 ≤ -ξ₁ ^ 2 * θ' ξ₁ ∧ -ξ₁ ^ 2 * θ' ξ₁ ≤ 2.4110460122) ∧
      (11.402542860 ≤ ξ₁ ^ 3 / (3 * (-ξ₁ ^ 2 * θ' ξ₁)) ∧
        ξ₁ ^ 3 / (3 * (-ξ₁ ^ 2 * θ' ξ₁)) ≤ 11.402542864) := by
  sorry

end Work.Math.LaneEmden2Blind
