import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Checked.Townes.TownesShooting
import Checked.Townes.TExAssemble
/-! Townes ground state, `TownesExists`: existence of a ground state of the Townes radial equation with central value in the bracket printed in the statement of `townes_exists`. Promoted from `Work/Townes/TownesExists.lean`. -/

namespace Checked.Townes.Exists
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
  Checked.Townes.TExAssemble.core Checked.Townes.Shooting.townes_under Checked.Townes.Shooting.townes_over

end Checked.Townes.Exists
