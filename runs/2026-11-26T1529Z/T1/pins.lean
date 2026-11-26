import ComparatorChallenges.NavierStokes

/-! Target 1 pins: the frozen solution notions are satisfiable (zero data, zero force: the zero
solution qualifies on ℝ³ and on the torus), so "no solution exists" in the frozen theorems is not
true for a junk reason; the data conditions are satisfiable by the zero data too; and `∞` in
`ContDiff ℝ ∞` is smoothness (C^∞), not analyticity (ω). -/
open scoped ContDiff Laplacian
open Set MeasureTheory NavierStokes.Comparator

namespace ExternalT1.Pins
abbrev E := EuclideanSpace ℝ (Fin 3)

theorem zero_solution_R3 (ν : ℝ) :
    NavierStokesExistenceAndSmoothnessRn ν (0 : E → E) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) where
  navier_stokes := fun x t _ => by simp [gradient]
  div_free := fun x t _ => by simpa using divergence_zero (n := 3) x
  initial_condition := fun _ => rfl
  velocity_smooth := contDiffOn_const
  pressure_smooth := contDiffOn_const
  integrable := fun _ _ => by simpa using (MemLp.zero : MemLp (0 : E → ℝ) 2)
  globally_bounded_energy := ⟨1, fun _ _ => by simp⟩

theorem zero_data_R3 : InitialVelocityConditionDecay (0 : E → E) ∧
    ForceConditionDecay (fun (_ : E) (_ : ℝ) => (0 : E)) := by
  refine ⟨⟨⟨fun x => divergence_zero x, contDiff_const⟩, fun m K => ⟨0, fun x => ?_⟩⟩,
    ⟨⟨contDiffOn_const⟩, fun m K => ⟨0, fun x t _ => ?_⟩⟩⟩
  · simp [iteratedFDeriv_zero_fun]
  · have : (↿(fun (_ : E) (_ : ℝ) => (0 : E))) = fun _ => 0 := rfl
    rw [this, iteratedFDerivWithin_zero_fun]; simp

theorem smooth_not_analytic : (∞ : WithTop ℕ∞) ≠ ω := by decide

end ExternalT1.Pins
#print axioms ExternalT1.Pins.zero_solution_R3
#print axioms ExternalT1.Pins.zero_data_R3
