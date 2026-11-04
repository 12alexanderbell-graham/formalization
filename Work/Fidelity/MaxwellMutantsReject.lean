import Work.Fidelity.MaxwellSpec
import Work.Fidelity.MaxwellMutants

/-!
# Red-team mutants of `IsMaxwellCoexistence` refuted by the blind spec (run 2026-11-04T0028Z)

Mutants: `Work/Fidelity/MaxwellMutants.lean` (Sonnet red team, run 2026-10-31T1428Z, blind to
the spec; frozen copy). Spec: `Work/Fidelity/MaxwellSpec.lean` (blind, frozen copy).
`reject_NN : ¬ MaxwellSpec mutantNN` — the spec catches the mutant.

This run: 01, 02, 03, 04, 06, 08, 09 (cubic-loop anchors and near misses; the determining law on
explicit polynomial isotherms). Open: 05, 07, 10 (absolute-value integrals; density variable).
-/

namespace Work.Fidelity.MaxwellMutantsReject

open Work.Fidelity.MaxwellSpec RedTeam.Maxwell

/-- 01 (non-strict order) violates `coincident`. -/
theorem reject_01 : ¬ MaxwellSpec mutant01 := by
  intro h
  apply h.coincident (fun _ => 1) 1 1
    (physDomain_of_continuous continuous_const one_pos one_pos)
  unfold mutant01
  refine ⟨le_rfl, rfl, rfl, ?_⟩
  simp

/-- 03 (sign of `p v` in the Gibbs energy) violates the `cubic_loop` anchor. -/
theorem reject_03 : ¬ MaxwellSpec mutant03 := by
  intro h
  have m := h.cubic_loop 1 1 2 1 one_pos one_pos one_lt_two
  have r := ref_satisfies.cubic_loop 1 1 2 1 one_pos one_pos one_lt_two
  unfold mutant03 at m
  unfold MRef at r
  obtain ⟨-, -, -, hm⟩ := m
  obtain ⟨-, -, -, hr⟩ := r
  linarith

/-- 04 (equal Helmholtz energies) violates the `cubic_loop` anchor. -/
theorem reject_04 : ¬ MaxwellSpec mutant04 := by
  intro h
  have m := h.cubic_loop 1 1 2 1 one_pos one_pos one_lt_two
  have r := ref_satisfies.cubic_loop 1 1 2 1 one_pos one_pos one_lt_two
  unfold mutant04 at m
  unfold MRef at r
  obtain ⟨-, -, -, hm⟩ := m
  obtain ⟨-, -, -, hr⟩ := r
  linarith

/-- 08 (one-sided area condition) violates the `unequal_areas` near miss (loop with `d = −1`). -/
theorem reject_08 : ¬ MaxwellSpec mutant08 := by
  intro h
  apply h.unequal_areas 1 1 2 1 (-1) one_pos one_pos one_lt_two (by norm_num)
  unfold mutant08
  refine ⟨by norm_num, by norm_num [cubicLoop], by norm_num [cubicLoop], ?_⟩
  rw [loop_integral]
  norm_num [loopAnti]

/-- 09 (swapped phase labels) violates the `cubic_loop` anchor. -/
theorem reject_09 : ¬ MaxwellSpec mutant09 := by
  intro h
  have m := h.cubic_loop 1 1 2 1 one_pos one_pos one_lt_two
  unfold mutant09 at m
  linarith [m.1]

/-- 06 (gas-side pressure condition dropped) is caught by the determining law: on the loop
`cubicLoop 1 1 2 1 (-3/8)` the pair `(1, 2)` has `p 1 = 1` and `∫₁² (p − 1) = 0`, but `p 2 = 11/8`. -/
theorem reject_06 : ¬ MaxwellSpec mutant06 := by
  intro h
  have hD : PhysDomain (cubicLoop 1 1 2 1 (-3 / 8)) 1 2 :=
    physDomain_of_continuous (cubicLoop_continuous _ _ _ _ _) one_pos two_pos
  have hm : mutant06 (cubicLoop 1 1 2 1 (-3 / 8)) 1 2 1 := by
    unfold mutant06
    refine ⟨by norm_num, by norm_num [cubicLoop], ?_⟩
    rw [intervalIntegral.integral_sub (cubicLoop_continuous _ _ _ _ _).intervalIntegrable
      intervalIntegrable_const, loop_integral, intervalIntegral.integral_const]
    norm_num [loopAnti, smul_eq_mul]
  obtain ⟨-, -, h3, -⟩ := (h.determining _ 1 2 1 hD).1 hm
  norm_num [cubicLoop] at h3

/-- The quartic isotherm `(v−1)(v−2)(v−3)(v−4)` (zero at 1, 2, 3). -/
noncomputable def quart (v : ℝ) : ℝ := (v - 1) * (v - 2) * (v - 3) * (v - 4)

theorem quart_continuous : Continuous quart := by unfold quart; fun_prop

theorem quart_hasDerivAt (v : ℝ) :
    HasDerivAt (fun v : ℝ => (v - 2) ^ 5 / 5 - (v - 2) ^ 4 / 2 - (v - 2) ^ 3 / 3 + (v - 2) ^ 2)
      (quart v) v := by
  have hu : HasDerivAt (fun w : ℝ => w - 2) 1 v := (hasDerivAt_id v).sub_const 2
  have h5 := (hu.pow 5).div_const 5
  have h4 := (hu.pow 4).div_const 2
  have h3 := (hu.pow 3).div_const 3
  have h2 := hu.pow 2
  convert ((h5.sub h4).sub h3).add h2 using 1
  simp [quart]
  ring

/-- 02 (midpoint pressure instead of equal areas) is caught by the determining law: the quartic
has `p 1 = p 2 = p 3 = 0` but `∫₁³ p = −4/15`. -/
theorem reject_02 : ¬ MaxwellSpec mutant02 := by
  intro h
  have hD : PhysDomain quart 1 3 := physDomain_of_continuous quart_continuous one_pos (by norm_num)
  have hm : mutant02 quart 1 3 0 := by
    unfold mutant02
    refine ⟨by norm_num, by norm_num [quart], by norm_num [quart], by norm_num [quart]⟩
  obtain ⟨-, -, -, hI⟩ := (h.determining quart 1 3 0 hD).1 hm
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => quart_hasDerivAt v)
    (quart_continuous.intervalIntegrable 1 3)] at hI
  norm_num at hI

end Work.Fidelity.MaxwellMutantsReject
