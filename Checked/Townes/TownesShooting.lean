import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Checked.Townes.TQDataA
import Checked.Townes.TQDataB
/-! Townes ground state, `TownesShooting`: the two shooting events of the Townes radial equation, undershoot and overshoot, as printed in the statements of `townes_under` and `townes_over`. Promoted from `Work/Townes/TownesShooting.lean`. -/

namespace Checked.Townes.Shooting
open Set

/-- Townes radial equation, undershoot: for every S ≥ 68/5 and every solution θ of
θ'' + (1/r)θ' − θ + θ³ = 0 on (0, S] with θ(0) = 2.2062008646, θ differentiable on [0, S] with
derivative φ and φ continuous at 0, there is r in (0, 68/5] with φ(r) > 0 and θ positive on
[0, r]. -/
theorem townes_under (S : ℝ) (hS : 68 / 5 ≤ S) (θ φ : ℝ → ℝ)
    (hθ : ∀ r ∈ Icc (0 : ℝ) S, HasDerivWithinAt θ (φ r) (Icc 0 S) r)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ r ∈ Ioc (0 : ℝ) S, HasDerivWithinAt φ (-(1 / r * φ r) + θ r - θ r ^ 3) (Icc 0 S) r)
    (h0 : θ 0 = 2.2062008646) :
    ∃ r ∈ Ioc (0 : ℝ) (68 / 5), 0 < φ r ∧ ∀ s ∈ Icc 0 r, 0 < θ s := by
  have hsub : Icc (0 : ℝ) (68 / 5) ⊆ Icc 0 S := Icc_subset_Icc le_rfl hS
  obtain ⟨hpos, hφe⟩ := Checked.Townes.TQDataA.chain (θ := θ) (φ := φ)
    (fun s hs => (hθ s (hsub hs)).mono hsub) (hφ0.mono hsub)
    (fun s hs => (hφ s ⟨hs.1, hs.2.trans hS⟩).mono hsub) (by rw [h0]; norm_num)
  exact ⟨68 / 5, ⟨by norm_num, le_rfl⟩, hφe, hpos⟩

/-- Townes radial equation, overshoot: for every S ≥ 68/5 and every solution θ of
θ'' + (1/r)θ' − θ + θ³ = 0 on (0, S] with θ(0) = 2.2062008647, θ differentiable on [0, S] with
derivative φ and φ continuous at 0, there is r in (0, 68/5] with θ(r) < 0 and φ negative on
(0, r]. -/
theorem townes_over (S : ℝ) (hS : 68 / 5 ≤ S) (θ φ : ℝ → ℝ)
    (hθ : ∀ r ∈ Icc (0 : ℝ) S, HasDerivWithinAt θ (φ r) (Icc 0 S) r)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ r ∈ Ioc (0 : ℝ) S, HasDerivWithinAt φ (-(1 / r * φ r) + θ r - θ r ^ 3) (Icc 0 S) r)
    (h0 : θ 0 = 2.2062008647) :
    ∃ r ∈ Ioc (0 : ℝ) (68 / 5), θ r < 0 ∧ ∀ s ∈ Ioc 0 r, φ s < 0 := by
  have hsub : Icc (0 : ℝ) (68 / 5) ⊆ Icc 0 S := Icc_subset_Icc le_rfl hS
  obtain ⟨hneg, hθe⟩ := Checked.Townes.TQDataB.chain (θ := θ) (φ := φ)
    (fun s hs => (hθ s (hsub hs)).mono hsub) (hφ0.mono hsub)
    (fun s hs => (hφ s ⟨hs.1, hs.2.trans hS⟩).mono hsub) (by rw [h0]; norm_num)
  exact ⟨68 / 5, ⟨by norm_num, le_rfl⟩, hθe, hneg⟩

end Checked.Townes.Shooting
