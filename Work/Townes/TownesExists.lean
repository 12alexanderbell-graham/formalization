import Mathlib
import Work.Townes.TownesShooting
import Work.Townes.TExAssemble

/-!
# Mathematics (THE RESULT parts 5 and 2): existence of the Townes ground state with central
# value in the certified bracket (frozen before proof, run 2026-11-07T0628Z)

**Question.** The Townes soliton is the positive radial ground state Q of ΔQ − Q + Q³ = 0 in the
plane. Its radial profile θ solves
  θ'' + (1/r) θ' − θ + θ³ = 0 on (0, ∞),  θ'(0) = 0,  θ > 0,  θ(r) → 0 as r → ∞.
Run 2026-11-07T0228Z proved the two shooting events (`Work.Townes.Shooting.townes_under`,
`townes_over`): every solution with θ(0) = 2.2062008646 turns back up before reaching zero, every
solution with θ(0) = 2.2062008647 crosses zero while decreasing. Those statements say nothing
about whether a ground state exists in between.

**What is stated here.** There is a central value c strictly between 2.2062008646 and
2.2062008647 and a solution (θ, φ = θ') on [0, ∞) with θ(0) = c, φ(0) = 0, φ continuous at 0,
θ differentiable on [0, ∞) (one-sided at 0) with derivative φ, φ' = −(1/r)φ + θ − θ³ on
(0, ∞), θ positive on [0, ∞), φ negative on (0, ∞), and θ(r) → 0 as r → ∞: a positive,
strictly decreasing, decaying radial solution, i.e. a ground state, whose central value lies in
the bracket. Uniqueness of the positive decaying radial solution (Kwong 1989) is not formalised,
so the statement does not by itself say that this is the only ground state.

Only Mathlib definitions occur in the statement.
-/

namespace Work.Townes.Exists
open Set Filter Topology

/-- Townes radial equation, existence: there is c in (2.2062008646, 2.2062008647) and a solution
θ of θ'' + (1/r)θ' − θ + θ³ = 0 on (0, ∞) with θ(0) = c, derivative φ on [0, ∞) (one-sided at 0),
φ(0) = 0 and φ continuous at 0, θ positive on [0, ∞), φ negative on (0, ∞) and θ(r) → 0 as
r → ∞. -/
theorem townes_exists : ∃ c ∈ Ioo (2.2062008646 : ℝ) 2.2062008647, ∃ θ φ : ℝ → ℝ,
    θ 0 = c ∧ φ 0 = 0 ∧
    (∀ r ∈ Ici (0 : ℝ), HasDerivWithinAt θ (φ r) (Ici 0) r) ∧
    ContinuousWithinAt φ (Ici 0) 0 ∧
    (∀ r ∈ Ioi (0 : ℝ), HasDerivAt φ (-(1 / r * φ r) + θ r - θ r ^ 3) r) ∧
    (∀ r ∈ Ici (0 : ℝ), 0 < θ r) ∧ (∀ r ∈ Ioi (0 : ℝ), φ r < 0) ∧
    Tendsto θ atTop (𝓝 0) :=
  Work.Townes.TExAssemble.core Work.Townes.Shooting.townes_under Work.Townes.Shooting.townes_over

end Work.Townes.Exists
