import Work.Fidelity.MaxwellSpec
import Work.Chemistry.Coexistence

/-!
# The program's `IsMaxwellCoexistence` meets the blind Maxwell spec, and the spec pins it
(run 2026-11-04T0028Z; fidelity protocol, PROMPT working note "Pinning protocol")

* `isMaxwellCoexistence_meets`: the program's definition
  `Work.Chemistry.Coexistence.IsMaxwellCoexistence` satisfies every field of the blind spec
  `Work.Fidelity.MaxwellSpec.MaxwellSpec` (frozen copy of the run-1428Z spec).
* `maxwellSpec_pins`: any predicate meeting the spec agrees with the program's definition on the
  spec's physical domain. The proof uses only the **equal-chemical-potential law** (equal pressure
  and equal `μ = f + p v` for a Helmholtz energy `f` with `∂f/∂v = −p`), applied to
  `f v = −∫_{vl}^{v} p`; it does not use the spec's equal-area field, which restates the definition.

To be copied verbatim to `Checked/Fidelity/` at promotion.
-/

namespace Work.Fidelity.MaxwellPin

open Work.Fidelity.MaxwellSpec Work.Chemistry.Coexistence

/-- The program's definition meets every field of the blind Maxwell spec. -/
theorem isMaxwellCoexistence_meets : MaxwellSpec IsMaxwellCoexistence :=
  of_determining (fun _ _ _ _ _ => Iff.rfl)

/-- Pinning from the equal-chemical-potential law alone: on the physical domain (positive
volumes, isotherm continuous near the tie line) any predicate meeting the spec is Maxwell
coexistence as the program defines it. -/
theorem maxwellSpec_pins (M : (ℝ → ℝ) → ℝ → ℝ → ℝ → Prop) (hM : MaxwellSpec M)
    (p : ℝ → ℝ) (vl vg ps : ℝ) (hD : PhysDomain p vl vg) :
    M p vl vg ps ↔ IsMaxwellCoexistence p vl vg ps := by
  have hD2 := hD
  obtain ⟨-, -, U, hU, hs, hc⟩ := hD2
  have hderiv : ∀ v ∈ Set.uIcc vl vg,
      HasDerivAt (fun u => -∫ t in vl..u, p t) (-p v) v := by
    intro v hv
    have hvU : v ∈ U := hs hv
    have hcont : ContinuousAt p v := hc.continuousAt (hU.mem_nhds hvU)
    have hint : IntervalIntegrable p MeasureTheory.volume vl v :=
      (hc.mono ((Set.uIcc_subset_uIcc_left hv).trans hs)).intervalIntegrable
    have hmeas : StronglyMeasurableAtFilter p (nhds v) MeasureTheory.volume :=
      hc.stronglyMeasurableAtFilter hU v hvU
    exact (intervalIntegral.integral_hasDerivAt_right hint hmeas hcont).neg
  rw [hM.equal_chemical_potential p _ vl vg ps hD hderiv]
  unfold IsMaxwellCoexistence
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, ?_⟩
    simp only [intervalIntegral.integral_same, neg_zero, zero_add] at h4
    linear_combination h4
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, ?_⟩
    simp only [intervalIntegral.integral_same, neg_zero, zero_add]
    linear_combination h4

end Work.Fidelity.MaxwellPin

-- Axiom report for the run record (printed in the CI build log).
#print axioms Work.Chemistry.Coexistence.vdW_coexistence_exists
#print axioms Work.Chemistry.Coexistence.vdW_coexistence_unique
#print axioms Work.Fidelity.MaxwellPin.maxwellSpec_pins
