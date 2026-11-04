import Checked.Sim.MichaelisMenten
import Checked.Fidelity.MMSpec

/-!
# Pin of `IsMMSolution` by the blind spec `MMSpec`

The spec (`Checked/Fidelity/MMSpec.lean`, copied verbatim from the blind
`Work/Fidelity/MMSpec.lean`, run 2026-11-04T0828Z) was written from the interface alone; its
determining law is the mass-action rate system of E + S ⇌ C → E + P with derivatives within
[0, T]; its other fields (integral form, enzyme and mass conservation, closed-form anchors with
no binding or no enzyme, a nonlinear binding anchor, seven near misses) are proved for its own
reference. The pin: any predicate meeting the spec is the program's `IsMMSolution`, and
`IsMMSolution` meets the spec.
-/

namespace Checked.Sim.MMPin
open Set

theorem isMM_eq_ref :
    Checked.Sim.MichaelisMenten.IsMMSolution = Checked.Fidelity.MMSpec.refMM := by
  funext k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p
  unfold Checked.Sim.MichaelisMenten.IsMMSolution Checked.Fidelity.MMSpec.refMM
  have e1 : ∀ t, -k₁ * e t * s t + km₁ * c t = -(k₁ * e t * s t) + km₁ * c t := fun t => by ring
  have e2 : ∀ t, -k₁ * e t * s t + (km₁ + k₂) * c t = -(k₁ * e t * s t) + (km₁ + k₂) * c t :=
    fun t => by ring
  simp only [e1, e2]

/-- The program's Michaelis–Menten predicate meets the blind specification. -/
theorem isMM_meets : Checked.Fidelity.MMSpec.MMSpec Checked.Sim.MichaelisMenten.IsMMSolution := by
  rw [isMM_eq_ref]; exact Checked.Fidelity.MMSpec.refMM_meets

/-- Every predicate meeting the blind Michaelis–Menten spec agrees with the program's
`IsMMSolution` on all arguments (the spec determines the definition). -/
theorem mmSpec_pins {P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ →
    (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → Prop} (hP : Checked.Fidelity.MMSpec.MMSpec P)
    (k₁ km₁ k₂ s₀ e₀ c₀ p₀ T : ℝ) (s e c p : ℝ → ℝ) :
    P k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p ↔
      Checked.Sim.MichaelisMenten.IsMMSolution k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p := by
  rw [isMM_eq_ref]; exact Checked.Fidelity.MMSpec.spec_pins hP k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p

end Checked.Sim.MMPin
