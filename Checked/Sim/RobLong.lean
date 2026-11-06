import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Bound
import Checked.Sim.Robertson
import Checked.Sim.RobLChain
import Checked.Sim.RobExistsLong

/-!
# Robertson's stiff network at t = 10¹¹

Robertson's (1966) network with the standard constants k₁ = 1/25, k₂ = 10⁴, k₃ = 3·10⁷ and
y(0) = (1, 0, 0) (`Checked.Sim.Robertson.IsRobSolution`) is the standard stiff test problem ROBER;
the Bari IVP test set integrates it on [0, 10¹¹] and prints a floating-point reference solution at
t = 10¹¹ (Mazzia & Magherini, Bari IVP test set report, problem ROBER, computed with RADAU; typeset
crops in `runs/2026-11-06T0828Z/typeset/`). No rigorous enclosure at any t ≥ 10³ was found in the
literature (prior-art screen, `runs/2026-11-06T0828Z/reader_rober.md`).

Statements are about *every* solution of the rate equations on [0, 10¹¹] (derivatives within the
interval); existence is a separate statement. The certified intervals fix the first ten digits of
y₁(10¹¹), the first five of y₂(10¹¹) and fourteen decimals of y₃(10¹¹). The printed reference
y₃ = 0.9999999791665050 lies more than 10⁻¹⁴ below every solution's y₃(10¹¹) (the printed triple
violates y₁ + y₂ + y₃ = 1 by about 10⁻¹⁴). The printed y₁, y₂ have relative errors of the same
order (referee, `runs/2026-11-06T0828Z/referee_robL.md`) but lie inside their certified intervals,
which are wider in relative terms; the reference is good to about 14 digits and prints 16.

Promoted from `Work/Sim/RobLong.lean` (frozen in run 2026-11-06T0828Z; statements identical up to
the namespace) by `runs/2026-11-06T1028Z/scripts/promote_robL.py`.

Method: `Checked.Sim.Robertson.chain` to t = 40, then 77 generated cells
(`runs/2026-11-06T0828Z/scripts/gen_robL.py`, `emit_robL.py`) of the contracting sheared-weight
step `Checked.Sim.RobShear.stepS` with Chebyshev defect bounds (`Checked.Sim.ChebBound`).
-/

namespace Checked.Sim.RobLong
open Set

/-- Componentwise enclosure at t = 10¹¹ and conservation, for every solution. -/
theorem enclosure {y₁ y₂ y₃ : ℝ → ℝ}
    (h : Checked.Sim.Robertson.IsRobSolution (1 / 25) 10000 30000000 1 0 0 100000000000 y₁ y₂ y₃) :
    |y₂ 100000000000 - (833336077033477183745690879 / 10000000000000000000000000000000000000000 : ℝ)| ≤ (7 / 5000000000000000000 : ℝ) / 10 ∧
    |y₃ 100000000000 - (9999999791665151693793832545318638393189 / 10000000000000000000000000000000000000000 : ℝ)| ≤ (7 / 5000000000000000000 : ℝ) + |(399998912391 / 1000000000000000 : ℝ)| * ((7 / 5000000000000000000 : ℝ) / 10) ∧
    y₁ 100000000000 = 1 - y₂ 100000000000 - y₃ 100000000000 := by
  obtain ⟨h1, h2, h3, hd⟩ := h
  have hM := Checked.Sim.Robertson.const_of_zero (F := fun t => y₁ t + y₂ t + y₃ t)
    (T := 100000000000) (fun t ht => by
      have := ((hd t ht).1.add (hd t ht).2.1).add (hd t ht).2.2
      convert this using 1; ring)
  have hy1 : ∀ t ∈ Icc (0 : ℝ) 100000000000, y₁ t = 1 - y₂ t - y₃ t := fun t ht => by
    have := hM t ht; simp only [h1, h2, h3] at this; linarith
  have hd2 : ∀ t ∈ Icc (0 : ℝ) 100000000000, HasDerivWithinAt y₂
      (Checked.Sim.RobCell.robP (y₂ t) (y₃ t)) (Icc 0 100000000000) t := fun t ht => by
    have := (hd t ht).2.1
    convert this using 1
    rw [hy1 t ht]; unfold Checked.Sim.RobCell.robP; ring
  have hd3 : ∀ t ∈ Icc (0 : ℝ) 100000000000, HasDerivWithinAt y₃
      (Checked.Sim.RobCell.robQ (y₂ t) (y₃ t)) (Icc 0 100000000000) t := fun t ht => by
    have := (hd t ht).2.2
    convert this using 1
    unfold Checked.Sim.RobCell.robQ; ring
  obtain ⟨-, a, b⟩ := Checked.Sim.RobLChain.finalL (fun _ _ _ _ _ _ => ⟨rfl, rfl⟩) hd2 hd3 h2 h3
  exact ⟨a, b, hy1 _ ⟨by norm_num, le_rfl⟩⟩

/-- Certified state of Robertson's stiff network at t = 10¹¹: for k₁ = 1/25, k₂ = 10⁴,
k₃ = 3·10⁷ and initial concentrations (1, 0, 0), every solution of the rate equations on
[0, 10¹¹] has 0.000000020833401494 < y₁(10¹¹) < 0.0000000208334015,
0.000000000000083333 < y₂(10¹¹) < 0.000000000000083334 and
0.99999997916651 < y₃(10¹¹) < 0.99999997916652. -/
theorem rob_state1e11 {y₁ y₂ y₃ : ℝ → ℝ}
    (h : Checked.Sim.Robertson.IsRobSolution (1 / 25) 10000 30000000 1 0 0 100000000000 y₁ y₂ y₃) :
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
    (h : Checked.Sim.Robertson.IsRobSolution (1 / 25) 10000 30000000 1 0 0 100000000000 y₁ y₂ y₃) :
    9999999791665050 / 10000000000000000 + 1 / 100000000000000 < y₃ 100000000000 := by
  obtain ⟨-, a3, -⟩ := enclosure h
  rw [abs_le] at a3
  norm_num at a3 ⊢
  linarith [a3.1]

/-- There is a solution of the rate equations of Robertson's network on [0, 10¹¹] with
k₁ = 1/25, k₂ = 10⁴, k₃ = 3·10⁷ and initial concentrations (1, 0, 0). -/
theorem rob_exists_1e11 : ∃ y₁ y₂ y₃ : ℝ → ℝ,
    Checked.Sim.Robertson.IsRobSolution (1 / 25) 10000 30000000 1 0 0 100000000000 y₁ y₂ y₃ := by
  obtain ⟨α, h0, hα⟩ := Checked.Sim.RobExistsLong.exists_clamped_long
  have hd2 : ∀ t ∈ Icc (0 : ℝ) 100000000000, HasDerivWithinAt (fun s => (α s).1)
      ((fun a b => (Checked.Sim.RobExists.Φc (a, b)).1) ((α t).1) ((α t).2)) (Icc 0 100000000000) t :=
    fun t ht => by simpa using Checked.Sim.Robertson.fstW (hα t ht)
  have hd3 : ∀ t ∈ Icc (0 : ℝ) 100000000000, HasDerivWithinAt (fun s => (α s).2)
      ((fun a b => (Checked.Sim.RobExists.Φc (a, b)).2) ((α t).1) ((α t).2)) (Icc 0 100000000000) t :=
    fun t ht => by simpa using Checked.Sim.Robertson.sndW (hα t ht)
  obtain ⟨hbox, -⟩ := Checked.Sim.RobLChain.chainL (P := fun a b => (Checked.Sim.RobExists.Φc (a, b)).1)
    (Q := fun a b => (Checked.Sim.RobExists.Φc (a, b)).2) Checked.Sim.Robertson.Φc_eq hd2 hd3
    (by simp [h0]) (by simp [h0])
  refine ⟨fun t => 1 - (α t).1 - (α t).2, fun t => (α t).1, fun t => (α t).2,
    by simp [h0], by simp [h0], by simp [h0], fun t ht => ?_⟩
  obtain ⟨b1, b2, b3, b4⟩ := hbox t ht
  obtain ⟨e1, e2⟩ := Checked.Sim.Robertson.Φc_eq _ _ b1 b2 b3 b4
  have k2 := hd2 t ht
  have k3 := hd3 t ht
  simp only at k2 k3
  rw [e1] at k2
  rw [e2] at k3
  refine ⟨?_, ?_, ?_⟩
  · convert ((hasDerivWithinAt_const t _ (1 : ℝ)).sub k2).sub k3 using 1
    unfold Checked.Sim.RobCell.robP Checked.Sim.RobCell.robQ; ring
  · convert k2 using 1; unfold Checked.Sim.RobCell.robP; ring
  · convert k3 using 1; unfold Checked.Sim.RobCell.robQ; rfl

end Checked.Sim.RobLong

#print axioms Checked.Sim.RobLong.rob_state1e11
#print axioms Checked.Sim.RobLong.rob_printed_y3_low
#print axioms Checked.Sim.RobLong.rob_exists_1e11
