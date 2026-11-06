import Mathlib

/-!
# Robertson's stiff reaction network: certified state at t = 40 (FROZEN statements)

THE RESULT part 1 ("rigorous simulators"), first stiff system. Robertson's (1966) network
A → B (rate constant k₁), B + C → A + C (k₂), 2B → B + C (k₃), with mass-action rate
equations for the concentrations y₁ = [A], y₂ = [B], y₃ = [C]:
y₁′ = −k₁ y₁ + k₂ y₂ y₃, y₂′ = k₁ y₁ − k₂ y₂ y₃ − k₃ y₂², y₃′ = k₃ y₂².
The standard stiff test problem takes k₁ = 0.04, k₂ = 10⁴, k₃ = 3·10⁷ and y(0) = (1, 0, 0).
The Jacobian has a stiff eigenvalue of size ≈ 2–3·10³ for most of [0, 40] (referee of run
2026-11-06T0428Z; ≈ −3.4·10³ at t = 40) against a slow one of size ≲ 1, so a classical Grönwall
enclosure (growth e^{Lt} with the full Lipschitz constant) is useless; the proof uses the
one-sided (logarithmic-norm) cell step `Work.Sim.OneSided.onesided_cell` in the weighted norm
4900·e₂² + e₃², in which the network is almost non-expanding.

Statements are about *every* solution of the rate equations on [0, 40] (derivatives within the
interval); existence is a separate statement.
-/

namespace Work.Sim.Robertson
open Set

/-- `IsRobSolution k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃`: the concentrations y₁ = [A], y₂ = [B],
y₃ = [C] solve the mass-action rate equations of Robertson's network A → B (k₁),
B + C → A + C (k₂), 2B → B + C (k₃) on the time interval [0, T]: initial values a₀, b₀, c₀ at
t = 0, and at every t ∈ [0, T] derivatives within [0, T]
y₁′ = −k₁ y₁ + k₂ y₂ y₃, y₂′ = k₁ y₁ − k₂ y₂ y₃ − k₃ y₂², y₃′ = k₃ y₂². -/
def IsRobSolution (k₁ k₂ k₃ a₀ b₀ c₀ T : ℝ) (y₁ y₂ y₃ : ℝ → ℝ) : Prop :=
  y₁ 0 = a₀ ∧ y₂ 0 = b₀ ∧ y₃ 0 = c₀ ∧ ∀ t ∈ Icc 0 T,
    HasDerivWithinAt y₁ (-k₁ * y₁ t + k₂ * y₂ t * y₃ t) (Icc 0 T) t ∧
    HasDerivWithinAt y₂ (k₁ * y₁ t - k₂ * y₂ t * y₃ t - k₃ * y₂ t ^ 2) (Icc 0 T) t ∧
    HasDerivWithinAt y₃ (k₃ * y₂ t ^ 2) (Icc 0 T) t

/-- Certified state of Robertson's stiff network at t = 40: for k₁ = 1/25, k₂ = 10⁴,
k₃ = 3·10⁷ and initial concentrations (1, 0, 0), every solution of the rate equations on
[0, 40] has 0.7158270 < y₁(40) < 0.7158271, 9.1855·10⁻⁶ < y₂(40) < 9.1856·10⁻⁶ and
0.2841637 < y₃(40) < 0.2841638. -/
theorem rob_state40 {y₁ y₂ y₃ : ℝ → ℝ}
    (h : IsRobSolution (1 / 25) 10000 30000000 1 0 0 40 y₁ y₂ y₃) :
    7158270 / 10000000 < y₁ 40 ∧ y₁ 40 < 7158271 / 10000000 ∧
    91855 / 10000000000 < y₂ 40 ∧ y₂ 40 < 91856 / 10000000000 ∧
    2841637 / 10000000 < y₃ 40 ∧ y₃ 40 < 2841638 / 10000000 := by
  sorry

/-- Robertson's network with k₁ = 1/25, k₂ = 10⁴, k₃ = 3·10⁷ and initial concentrations
(1, 0, 0) has a solution of the rate equations on [0, 40]. -/
theorem rob_exists : ∃ y₁ y₂ y₃ : ℝ → ℝ,
    IsRobSolution (1 / 25) 10000 30000000 1 0 0 40 y₁ y₂ y₃ := by
  sorry

end Work.Sim.Robertson
