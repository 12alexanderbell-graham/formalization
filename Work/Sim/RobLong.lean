import Mathlib
import Work.Sim.Robertson

/-!
# Robertson's stiff network at t = 10¹¹ (FROZEN statements, run 2026-11-06T0828Z)

THE RESULT parts 2 and 1. Robertson's (1966) network with the standard constants
k₁ = 0.04, k₂ = 10⁴, k₃ = 3·10⁷ and y(0) = (1, 0, 0) (`Work.Sim.Robertson.IsRobSolution`) is the
standard stiff test problem ROBER; the Bari IVP test set integrates it on [0, 10¹¹] and prints a
floating-point reference solution at t = 10¹¹ (Mazzia & Magherini, release 2.4, 2008, Table
II.10.3, computed with RADAU; crops in `runs/2026-11-06T0828Z/typeset/`). No rigorous enclosure at
any t ≥ 10³ was found in the literature (prior-art screen, `runs/2026-11-06T0828Z/reader_rober.md`).

Statements are about *every* solution of the rate equations on [0, 10¹¹] (derivatives within the
interval); existence is a separate statement. The certified values: y₁(10¹¹) to ten significant
digits, y₂(10¹¹) to five, y₃(10¹¹) to fourteen decimals. The printed reference y₃ = 0.9999999791665050
lies outside the certified interval for y₃ (it violates y₁ + y₂ + y₃ = 1 by 1.0·10⁻¹⁴);
the printed y₁, y₂ lie inside theirs.

Method: `Work.Sim.Robertson.chain` to t = 40, then 77 generated cells
(`runs/2026-11-06T0828Z/scripts/gen_robL.py`, `emit_robL.py`) of the contracting sheared-weight
step `Work.Sim.RobShear.stepS` with Chebyshev defect bounds (`Work.Sim.ChebBound`).
-/

namespace Work.Sim.RobLong
open Set

/-- Certified state of Robertson's stiff network at t = 10¹¹: for k₁ = 1/25, k₂ = 10⁴,
k₃ = 3·10⁷ and initial concentrations (1, 0, 0), every solution of the rate equations on
[0, 10¹¹] has 2.0833401494·10⁻⁸ < y₁(10¹¹) < 2.0833401500·10⁻⁸,
8.3333·10⁻¹⁴ < y₂(10¹¹) < 8.3334·10⁻¹⁴ and
0.99999997916651 < y₃(10¹¹) < 0.99999997916652. -/
theorem rob_state1e11 {y₁ y₂ y₃ : ℝ → ℝ}
    (h : Work.Sim.Robertson.IsRobSolution (1 / 25) 10000 30000000 1 0 0 100000000000 y₁ y₂ y₃) :
    20833401494 / 1000000000000000000 < y₁ 100000000000 ∧
    y₁ 100000000000 < 20833401500 / 1000000000000000000 ∧
    83333 / 1000000000000000000 < y₂ 100000000000 ∧
    y₂ 100000000000 < 83334 / 1000000000000000000 ∧
    99999997916651 / 100000000000000 < y₃ 100000000000 ∧
    y₃ 100000000000 < 99999997916652 / 100000000000000 := by
  sorry

/-- The printed reference value 0.9999999791665050 of the Bari IVP test set for the third
concentration of Robertson's network at t = 10¹¹ is false: no solution of the rate equations on
[0, 10¹¹] with k₁ = 1/25, k₂ = 10⁴, k₃ = 3·10⁷ and initial concentrations (1, 0, 0) takes that
value at t = 10¹¹. -/
theorem rob_printed_y3_false {y₁ y₂ y₃ : ℝ → ℝ}
    (h : Work.Sim.Robertson.IsRobSolution (1 / 25) 10000 30000000 1 0 0 100000000000 y₁ y₂ y₃) :
    y₃ 100000000000 ≠ 9999999791665050 / 10000000000000000 := by
  sorry

/-- Robertson's network with k₁ = 1/25, k₂ = 10⁴, k₃ = 3·10⁷ and initial concentrations
(1, 0, 0) has a solution of the rate equations on [0, 10¹¹]. -/
theorem rob_exists_1e11 : ∃ y₁ y₂ y₃ : ℝ → ℝ,
    Work.Sim.Robertson.IsRobSolution (1 / 25) 10000 30000000 1 0 0 100000000000 y₁ y₂ y₃ := by
  sorry

end Work.Sim.RobLong
