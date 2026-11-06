import Work.Sim.Robertson
import Work.Fidelity.RobSpec

/-!
# Pin of `IsRobSolution` by the blind spec `RobSpec`, and the literal agreement

The spec (`Work/Fidelity/RobSpec.lean`, run 2026-11-06T0428Z) was written from the interface
alone; its determining law is the mass-action rate system of Robertson's network with
derivatives within [0, T]. The pin: any predicate meeting the spec is the program's
`IsRobSolution`, and `IsRobSolution` meets the spec. The literal agreement compares the
constants of the frozen headlines with the blind literal reading
(`runs/2026-11-06T0428Z/rob_reader/SecondReadingRob.lean`, inlined here by value: Work does not
import `runs/`).
-/

namespace Work.Sim.RobPin
open Set

theorem isRob_eq_ref : Work.Sim.Robertson.IsRobSolution = Work.Fidelity.RobSpec.refRob := rfl

/-- The program's Robertson predicate meets the blind specification. -/
theorem isRob_meets : Work.Fidelity.RobSpec.RobSpec Work.Sim.Robertson.IsRobSolution := by
  rw [isRob_eq_ref]; exact Work.Fidelity.RobSpec.refRob_meets

/-- Every predicate meeting the blind Robertson spec agrees with `IsRobSolution`. -/
theorem robSpec_pins {P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → Prop}
    (hP : Work.Fidelity.RobSpec.RobSpec P) (k₁ k₂ k₃ a₀ b₀ c₀ T : ℝ) (y₁ y₂ y₃ : ℝ → ℝ) :
    P k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃ ↔
      Work.Sim.Robertson.IsRobSolution k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃ := by
  rw [isRob_eq_ref]; exact Work.Fidelity.RobSpec.spec_pins hP k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃

/-- The headline constants equal the blind reader's values (k₁ = 4/100, k₂ = 10⁴, k₃ = 3·10⁷,
initial (1, 0, 0), T = 40). -/
theorem literals_agree :
    (1 / 25 : ℝ) = 4 / 100 ∧ (10000 : ℝ) = 10 ^ 4 ∧ (30000000 : ℝ) = 3 * 10 ^ 7 ∧
      ((1 : ℝ), (0 : ℝ), (0 : ℝ)) = (1, 0, 0) ∧ (40 : ℝ) = 40 := by
  norm_num

end Work.Sim.RobPin
