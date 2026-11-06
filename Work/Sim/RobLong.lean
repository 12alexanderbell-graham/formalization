import Mathlib
import Work.Sim.Robertson
import Work.Sim.RobLChain
import Work.Sim.RobExistsLong

/-!
# Robertson's stiff network at t = 10¹¹ (FROZEN statements, run 2026-11-06T0828Z)

THE RESULT parts 2 and 1. Robertson's (1966) network with the standard constants
k₁ = 0.04, k₂ = 10⁴, k₃ = 3·10⁷ and y(0) = (1, 0, 0) (`Work.Sim.Robertson.IsRobSolution`) is the
standard stiff test problem ROBER; the Bari IVP test set integrates it on [0, 10¹¹] and prints a
floating-point reference solution at t = 10¹¹ (Mazzia & Magherini, release 2.4, 2008, Table
II.10.3, computed with RADAU; crops in `runs/2026-11-06T0828Z/typeset/`). No rigorous enclosure at
any t ≥ 10³ was found in the literature (prior-art screen, `runs/2026-11-06T0828Z/reader_rober.md`).

Statements are about *every* solution of the rate equations on [0, 10¹¹] (derivatives within the
interval); existence is a separate statement. The certified intervals fix the first ten digits of
y₁(10¹¹), the first five of y₂(10¹¹) and fourteen decimals of y₃(10¹¹). The printed reference
y₃ = 0.9999999791665050 lies more than 10⁻¹⁴ below every solution's y₃(10¹¹) (the printed triple
violates y₁ + y₂ + y₃ = 1 by 1.0·10⁻¹⁴). The printed y₁, y₂ have relative errors of the same order
(referee, `runs/2026-11-06T0828Z/referee_robL.md`) but lie inside their certified intervals, which
are wider in relative terms; the reference is good to about 14 digits and prints 16.
Statement change before proof (referee correction, LEDGER): the frozen `rob_printed_y3_false`
(y₃ ≠ printed, which the correctly rounded value would satisfy too) became the distance statement
`rob_printed_y3_low`.

Method: `Work.Sim.Robertson.chain` to t = 40, then 77 generated cells
(`runs/2026-11-06T0828Z/scripts/gen_robL.py`, `emit_robL.py`) of the contracting sheared-weight
step `Work.Sim.RobShear.stepS` with Chebyshev defect bounds (`Work.Sim.ChebBound`).
-/

namespace Work.Sim.RobLong
open Set

/-- Componentwise enclosure at t = 10¹¹ and conservation, for every solution. -/
theorem enclosure {y₁ y₂ y₃ : ℝ → ℝ}
    (h : Work.Sim.Robertson.IsRobSolution (1 / 25) 10000 30000000 1 0 0 100000000000 y₁ y₂ y₃) :
    |y₂ 100000000000 - (833336077033477183745690879 / 10000000000000000000000000000000000000000 : ℝ)| ≤ (7 / 5000000000000000000 : ℝ) / 10 ∧
    |y₃ 100000000000 - (9999999791665151693793832545318638393189 / 10000000000000000000000000000000000000000 : ℝ)| ≤ (7 / 5000000000000000000 : ℝ) + |(399998912391 / 1000000000000000 : ℝ)| * ((7 / 5000000000000000000 : ℝ) / 10) ∧
    y₁ 100000000000 = 1 - y₂ 100000000000 - y₃ 100000000000 := by
  obtain ⟨h1, h2, h3, hd⟩ := h
  have hM := Work.Sim.Robertson.const_of_zero (F := fun t => y₁ t + y₂ t + y₃ t)
    (T := 100000000000) (fun t ht => by
      have := ((hd t ht).1.add (hd t ht).2.1).add (hd t ht).2.2
      convert this using 1; ring)
  have hy1 : ∀ t ∈ Icc (0 : ℝ) 100000000000, y₁ t = 1 - y₂ t - y₃ t := fun t ht => by
    have := hM t ht; simp only [h1, h2, h3] at this; linarith
  have hd2 : ∀ t ∈ Icc (0 : ℝ) 100000000000, HasDerivWithinAt y₂
      (Work.Sim.RobCell.robP (y₂ t) (y₃ t)) (Icc 0 100000000000) t := fun t ht => by
    have := (hd t ht).2.1
    convert this using 1
    rw [hy1 t ht]; unfold Work.Sim.RobCell.robP; ring
  have hd3 : ∀ t ∈ Icc (0 : ℝ) 100000000000, HasDerivWithinAt y₃
      (Work.Sim.RobCell.robQ (y₂ t) (y₃ t)) (Icc 0 100000000000) t := fun t ht => by
    have := (hd t ht).2.2
    convert this using 1
    unfold Work.Sim.RobCell.robQ; ring
  obtain ⟨-, a, b⟩ := Work.Sim.RobLChain.finalL (fun _ _ _ _ _ _ => ⟨rfl, rfl⟩) hd2 hd3 h2 h3
  exact ⟨a, b, hy1 _ ⟨by norm_num, le_rfl⟩⟩

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
  obtain ⟨a2, a3, e1⟩ := enclosure h
  rw [abs_le] at a2 a3
  rw [e1]
  norm_num at a2 a3 ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith [a2.1, a2.2, a3.1, a3.2]

/-- The printed reference value 0.9999999791665050 of the Bari IVP test set for the third
concentration of Robertson's network at t = 10¹¹ is more than 10⁻¹⁴ too small: every solution of
the rate equations on [0, 10¹¹] with k₁ = 1/25, k₂ = 10⁴, k₃ = 3·10⁷ and initial concentrations
(1, 0, 0) has y₃(10¹¹) > 0.9999999791665050 + 10⁻¹⁴. -/
theorem rob_printed_y3_low {y₁ y₂ y₃ : ℝ → ℝ}
    (h : Work.Sim.Robertson.IsRobSolution (1 / 25) 10000 30000000 1 0 0 100000000000 y₁ y₂ y₃) :
    9999999791665050 / 10000000000000000 + 1 / 100000000000000 < y₃ 100000000000 := by
  obtain ⟨-, a3, -⟩ := enclosure h
  rw [abs_le] at a3
  norm_num at a3 ⊢
  linarith [a3.1]

/-- Robertson's network with k₁ = 1/25, k₂ = 10⁴, k₃ = 3·10⁷ and initial concentrations
(1, 0, 0) has a solution of the rate equations on [0, 10¹¹]. -/
theorem rob_exists_1e11 : ∃ y₁ y₂ y₃ : ℝ → ℝ,
    Work.Sim.Robertson.IsRobSolution (1 / 25) 10000 30000000 1 0 0 100000000000 y₁ y₂ y₃ := by
  obtain ⟨α, h0, hα⟩ := Work.Sim.RobExistsLong.exists_clamped_long
  have hd2 : ∀ t ∈ Icc (0 : ℝ) 100000000000, HasDerivWithinAt (fun s => (α s).1)
      ((fun a b => (Work.Sim.RobExists.Φc (a, b)).1) ((α t).1) ((α t).2)) (Icc 0 100000000000) t :=
    fun t ht => by simpa using Work.Sim.Robertson.fstW (hα t ht)
  have hd3 : ∀ t ∈ Icc (0 : ℝ) 100000000000, HasDerivWithinAt (fun s => (α s).2)
      ((fun a b => (Work.Sim.RobExists.Φc (a, b)).2) ((α t).1) ((α t).2)) (Icc 0 100000000000) t :=
    fun t ht => by simpa using Work.Sim.Robertson.sndW (hα t ht)
  obtain ⟨hbox, -⟩ := Work.Sim.RobLChain.chainL (P := fun a b => (Work.Sim.RobExists.Φc (a, b)).1)
    (Q := fun a b => (Work.Sim.RobExists.Φc (a, b)).2) Work.Sim.Robertson.Φc_eq hd2 hd3
    (by simp [h0]) (by simp [h0])
  refine ⟨fun t => 1 - (α t).1 - (α t).2, fun t => (α t).1, fun t => (α t).2,
    by simp [h0], by simp [h0], by simp [h0], fun t ht => ?_⟩
  obtain ⟨b1, b2, b3, b4⟩ := hbox t ht
  obtain ⟨e1, e2⟩ := Work.Sim.Robertson.Φc_eq _ _ b1 b2 b3 b4
  have k2 := hd2 t ht
  have k3 := hd3 t ht
  simp only at k2 k3
  rw [e1] at k2
  rw [e2] at k3
  refine ⟨?_, ?_, ?_⟩
  · convert ((hasDerivWithinAt_const t _ (1 : ℝ)).sub k2).sub k3 using 1
    unfold Work.Sim.RobCell.robP Work.Sim.RobCell.robQ; ring
  · convert k2 using 1; unfold Work.Sim.RobCell.robP; ring
  · convert k3 using 1; unfold Work.Sim.RobCell.robQ; rfl

end Work.Sim.RobLong

#print axioms Work.Sim.RobLong.rob_state1e11
#print axioms Work.Sim.RobLong.rob_printed_y3_low
#print axioms Work.Sim.RobLong.rob_exists_1e11
