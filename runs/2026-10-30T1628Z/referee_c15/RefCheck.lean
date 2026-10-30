import Checked.Cosmography.BambaZ
open Checked.Cosmography.BambaZ
-- verbatim copies of the frozen defs (Work/Cosmography/DemianskiZ.lean @ ab63005)
namespace RefC15
noncomputable def demDL4 (q j s l : ℝ) : ℝ :=
  (1 / 120) * (-6 + 6 * q + 81 * q ^ 2 + 165 * q ^ 3 - 105 * q ^ 4 - 110 * q * j
    + -105 * q ^ 2 * j - 15 * q * s - 27 * j + 10 * j ^ 2 - 11 * s - l)

noncomputable def demDA4 (q j s l : ℝ) : ℝ :=
  (1 / 120) * (274 + 326 * q + 411 * q ^ 2 + 315 * q ^ 3 + 105 * q ^ 4 - 210 * q * j
    - 105 * q ^ 2 * j - 15 * q * s + 137 * j + 10 * j ^ 2 - 21 * s - l)

-- referee spot check of the algebraic headline (independent of the frozen proof attempt)
example (q j s l : ℝ) :
    correctDL4z q j s l 0 - demDL4 q j s l = 7 / 4 * q ^ 4 ∧
    correctDA4z q j s l 0 - demDA4 q j s l = -(137 / 60) * j := by
  unfold correctDL4z printedDL4z demDL4 correctDA4z printedDA4z demDA4
  constructor <;> ring
-- literal reading of "+105q0^4 −  / −210q0j0" in (23) would be +210 q0 j0
noncomputable def demDA4lit (q j s l : ℝ) : ℝ :=
  (1 / 120) * (274 + 326 * q + 411 * q ^ 2 + 315 * q ^ 3 + 105 * q ^ 4 - (-210 * q * j)
    - 105 * q ^ 2 * j - 15 * q * s + 137 * j + 10 * j ^ 2 - 21 * s - l)
example (q j s l : ℝ) : correctDA4z q j s l 0 - demDA4lit q j s l = -(7/2) * q * j - (137/60) * j := by
  unfold correctDA4z printedDA4z demDA4lit; ring

end RefC15
