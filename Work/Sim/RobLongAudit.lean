import Work.Sim.RobLongBlind
import Work.Sim.RobLong
import Work.Sim.RobAudit

/-!
# Robertson at t = 10¹¹: blind restatement closed

The three statements of the blind restatement (`Work.Sim.RobLongBlind`, Sonnet, run
2026-11-06T0828Z) proved from the program's frozen theorems `Work.Sim.RobLong.rob_state1e11`,
`rob_printed_y3_low` and `rob_exists_1e11`. The blind reading asks for two-sided derivatives on
the open interval only (plus continuity on the closed one); the program's one-sided endpoint
derivatives follow from the limit of the derivative (`Work.Sim.RobAudit.within_Icc_of_interior`).
-/

namespace Work.Sim.RobLongAudit
open Set Filter Topology

theorem toProgram {y1 y2 y3 : ℝ → ℝ} (h : Work.Sim.RobLongBlind.IsSol (10 ^ 11) y1 y2 y3) :
    Work.Sim.Robertson.IsRobSolution (1 / 25) 10000 30000000 1 0 0 100000000000 y1 y2 y3 := by
  obtain ⟨c1, c2, c3, h1, h2, h3, hd⟩ := h
  have e : ((10 : ℝ) ^ 11) = 100000000000 := by norm_num
  rw [e] at c1 c2 c3 hd
  have hab : (0 : ℝ) < 100000000000 := by norm_num
  have d1 := Work.Sim.RobAudit.within_Icc_of_interior
    (f' := fun t => -(1 / 25 : ℝ) * y1 t + 10000 * y2 t * y3 t) hab c1 (by fun_prop)
    (fun t ht => (hd t ht).1)
  have d2 := Work.Sim.RobAudit.within_Icc_of_interior
    (f' := fun t => (1 / 25 : ℝ) * y1 t - 10000 * y2 t * y3 t - 30000000 * y2 t ^ 2)
    hab c2 (by fun_prop) (fun t ht => (hd t ht).2.1)
  have d3 := Work.Sim.RobAudit.within_Icc_of_interior (f' := fun t => 30000000 * y2 t ^ 2)
    hab c3 (by fun_prop) (fun t ht => (hd t ht).2.2)
  exact ⟨h1, h2, h3, fun t ht => ⟨d1 t ht, d2 t ht, d3 t ht⟩⟩

theorem blind_state1e11 (y1 y2 y3 : ℝ → ℝ) (h : Work.Sim.RobLongBlind.IsSol (10 ^ 11) y1 y2 y3) :
    (20833401494/10^18 : ℝ) < y1 (10^11) ∧ y1 (10^11) < 20833401500/10^18 ∧
    (83333/10^18 : ℝ) < y2 (10^11) ∧ y2 (10^11) < 83334/10^18 ∧
    (99999997916651/10^14 : ℝ) < y3 (10^11) ∧ y3 (10^11) < 99999997916652/10^14 := by
  have k := Work.Sim.RobLong.rob_state1e11 (toProgram h)
  norm_num at k ⊢
  exact k

theorem blind_y3_printed_false (y1 y2 y3 : ℝ → ℝ)
    (h : Work.Sim.RobLongBlind.IsSol (10 ^ 11) y1 y2 y3) :
    y3 (10^11) ≠ 9999999791665050/10^16 := by
  have k := Work.Sim.RobLong.rob_printed_y3_low (toProgram h)
  norm_num at k ⊢
  intro he; rw [he] at k; norm_num at k

theorem blind_exists1e11 : ∃ y1 y2 y3 : ℝ → ℝ, Work.Sim.RobLongBlind.IsSol (10 ^ 11) y1 y2 y3 := by
  obtain ⟨y₁, y₂, y₃, h1, h2, h3, hd⟩ := Work.Sim.RobLong.rob_exists_1e11
  have e : ((10 : ℝ) ^ 11) = 100000000000 := by norm_num
  refine ⟨y₁, y₂, y₃, ?_⟩
  unfold Work.Sim.RobLongBlind.IsSol
  rw [e]
  refine ⟨fun t ht => (hd t ht).1.continuousWithinAt,
    fun t ht => (hd t ht).2.1.continuousWithinAt, fun t ht => (hd t ht).2.2.continuousWithinAt,
    h1, h2, h3, fun t ht => ?_⟩
  have hn : Icc (0 : ℝ) 100000000000 ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have ht' : t ∈ Icc (0 : ℝ) 100000000000 := Ioo_subset_Icc_self ht
  refine ⟨?_, ?_, ?_⟩
  · have := ((hd t ht').1).hasDerivAt hn
    convert this using 1
  · exact ((hd t ht').2.1).hasDerivAt hn
  · exact ((hd t ht').2.2).hasDerivAt hn

end Work.Sim.RobLongAudit

#print axioms Work.Sim.RobLongAudit.blind_state1e11
#print axioms Work.Sim.RobLongAudit.blind_y3_printed_false
#print axioms Work.Sim.RobLongAudit.blind_exists1e11
