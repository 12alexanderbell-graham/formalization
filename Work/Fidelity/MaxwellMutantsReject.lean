import Work.Fidelity.MaxwellSpec
import Work.Fidelity.MaxwellMutants

/-!
# Red-team mutants of `IsMaxwellCoexistence` refuted by the blind spec (run 2026-11-04T0028Z)

Mutants: `Work/Fidelity/MaxwellMutants.lean` (Sonnet red team, run 2026-10-31T1428Z, blind to
the spec; frozen copy). Spec: `Work/Fidelity/MaxwellSpec.lean` (blind, frozen copy).
`reject_NN : ¬ MaxwellSpec mutantNN` — the spec catches the mutant.

This run: 01, 02, 03, 04, 05, 06, 08, 09, 10 (cubic-loop anchors and near misses; the determining
law on explicit polynomial isotherms, mirror symmetry for the unsigned-area mutants). 07 by the
`cubic_loop` anchor with an explicit log integral and a certified bound on log 3. All 10 refuted.
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
    rw [intervalIntegral.integral_sub ((cubicLoop_continuous _ _ _ _ _).intervalIntegrable _ _)
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

/-- The parabola isotherm `(v−1)(v−3)`, symmetric about `v = 2`. -/
noncomputable def quad (v : ℝ) : ℝ := (v - 1) * (v - 3)

theorem quad_continuous : Continuous quad := by unfold quad; fun_prop

theorem quad_hasDerivAt (v : ℝ) :
    HasDerivAt (fun v : ℝ => (v - 2) ^ 3 / 3 - (v - 2)) (quad v) v := by
  have hu : HasDerivAt (fun w : ℝ => w - 2) 1 v := (hasDerivAt_id v).sub_const 2
  have h3 := (hu.pow 3).div_const 3
  convert h3.sub hu using 1
  simp [quad]
  ring

/-- 05 (equal unsigned half-areas about the midpoint) is caught by the determining law: the
parabola `(v−1)(v−3)` is symmetric about 2, so its unsigned half-areas on `[1, 3]` agree, but
`∫₁³ p = −4/3`. -/
theorem reject_05 : ¬ MaxwellSpec mutant05 := by
  intro h
  have hD : PhysDomain quad 1 3 := physDomain_of_continuous quad_continuous one_pos (by norm_num)
  have hm : mutant05 quad 1 3 0 := by
    unfold mutant05
    refine ⟨by norm_num, by norm_num [quad], by norm_num [quad], ?_⟩
    have e : ((1:ℝ) + 3) / 2 = 2 := by norm_num
    rw [e]
    have hs := intervalIntegral.integral_comp_sub_left (f := fun v => |quad v - 0|)
      (a := (1:ℝ)) (b := 2) 4
    have e2 : (4:ℝ) - 2 = 2 := by norm_num
    have e3 : (4:ℝ) - 1 = 3 := by norm_num
    simp only [e2, e3] at hs
    rw [← hs]
    congr 1
    funext v
    unfold quad
    ring_nf
  obtain ⟨-, -, -, hI⟩ := (h.determining quad 1 3 0 hD).1 hm
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => quad_hasDerivAt v)
    (quad_continuous.intervalIntegrable 1 3)] at hI
  norm_num at hI

/-- The isotherm `(v−1)(v−3)(v−2)²`, symmetric about its double root 2. -/
noncomputable def sext (v : ℝ) : ℝ := (v - 1) * (v - 3) * (v - 2) ^ 2

theorem sext_continuous : Continuous sext := by unfold sext; fun_prop

theorem sext_hasDerivAt (v : ℝ) :
    HasDerivAt (fun v : ℝ => (v - 2) ^ 5 / 5 - (v - 2) ^ 3 / 3) (sext v) v := by
  have hu : HasDerivAt (fun w : ℝ => w - 2) 1 v := (hasDerivAt_id v).sub_const 2
  have h5 := (hu.pow 5).div_const 5
  have h3 := (hu.pow 3).div_const 3
  convert h5.sub h3 using 1
  simp [sext]
  ring

/-- 10 (equal unsigned lobes about an interior root) is caught by the determining law: on
`(v−1)(v−3)(v−2)²` the root 2 splits `[1, 3]` into mirror-image lobes, but `∫₁³ p = −4/15`. -/
theorem reject_10 : ¬ MaxwellSpec mutant10 := by
  intro h
  have hD : PhysDomain sext 1 3 := physDomain_of_continuous sext_continuous one_pos (by norm_num)
  have hm : mutant10 sext 1 3 0 := by
    unfold mutant10
    refine ⟨by norm_num, by norm_num [sext], by norm_num [sext], 2, by norm_num, by norm_num,
      by norm_num [sext], ?_⟩
    have hs := intervalIntegral.integral_comp_sub_left (f := fun v => |sext v - 0|)
      (a := (1:ℝ)) (b := 2) 4
    have e2 : (4:ℝ) - 2 = 2 := by norm_num
    have e3 : (4:ℝ) - 1 = 3 := by norm_num
    simp only [e2, e3] at hs
    rw [← hs]
    congr 1
    funext v
    unfold sext
    ring_nf
  obtain ⟨-, -, -, hI⟩ := (h.determining sext 1 3 0 hD).1 hm
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => sext_hasDerivAt v)
    (sext_continuous.intervalIntegrable 1 3)] at hI
  norm_num at hI

/-- Antiderivative of `cubicLoop 1 1 2 1 0 (1/ρ) = 7 − ρ⁻³ + 6ρ⁻² − 11ρ⁻¹` on `ρ > 0`. -/
noncomputable def G07 (ρ : ℝ) : ℝ := 7 * ρ + (ρ ^ 2)⁻¹ / 2 - 6 * ρ⁻¹ - 11 * Real.log ρ

/-- 07 (equal areas in the density variable, Jacobian dropped) violates the `cubic_loop` anchor:
on the symmetric loop with `(vl, vg, ps) = (1, 3, 1)` the density integral is
`∫_{1/3}^{1} p(1/ρ) dρ = 38/3 − 11 log 3`, which would force `log 3 = 12/11`; but
`log 3 > 1.094` (4-term series for `log (1 − 1/4)` and `log 2 > 0.6931471803`). -/
theorem reject_07 : ¬ MaxwellSpec mutant07 := by
  intro h
  have m := h.cubic_loop 1 1 2 1 one_pos one_pos one_lt_two
  unfold mutant07 at m
  obtain ⟨-, -, -, -, hI⟩ := m
  have e1 : (1:ℝ) / (2 + 1) = 1 / 3 := by norm_num
  have e2 : (1:ℝ) / (2 - 1) = 1 := by norm_num
  rw [e1, e2] at hI
  have hderiv : ∀ x ∈ Set.uIcc (1 / 3 : ℝ) 1,
      HasDerivAt G07 (cubicLoop 1 1 2 1 0 (1 / x)) x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    have hx0 : x ≠ 0 := ne_of_gt (by linarith [hx.1] : (0:ℝ) < x)
    have h1 := (hasDerivAt_id x).const_mul 7
    have h2 := ((hasDerivAt_pow 2 x).inv (pow_ne_zero 2 hx0)).div_const 2
    have h3 := (hasDerivAt_inv hx0).const_mul 6
    have h4 := (Real.hasDerivAt_log hx0).const_mul 11
    convert ((h1.add h2).sub h3).sub h4 using 1
    all_goals first
      | (funext y; simp [G07])
      | (simp only [cubicLoop, Nat.cast_ofNat, show (2:ℕ) - 1 = 1 from rfl, pow_one]
         field_simp
         ring)
  have hc : ContinuousOn (fun ρ : ℝ => 1 / ρ) (Set.uIcc (1 / 3 : ℝ) 1) := by
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    exact ne_of_gt (by linarith [hx.1] : (0:ℝ) < x)
  have hint := ((cubicLoop_continuous 1 1 2 1 0).comp_continuousOn hc).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint] at hI
  have g1 : G07 1 = 3 / 2 := by norm_num [G07]
  have g3 : G07 (1 / 3) = 7 / 3 + 9 / 2 - 18 + 11 * Real.log 3 := by
    unfold G07
    rw [one_div, Real.log_inv]
    ring
  rw [g1, g3] at hI
  -- log 3 = 2 log 2 + log (1 − 1/4) > 1.094
  have hl3 : Real.log 3 = 2 * Real.log 2 + Real.log (1 - 1 / 4) := by
    have e : (3:ℝ) = 2 ^ 2 * (1 - 1 / 4) := by norm_num
    conv_lhs => rw [e]
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Nat.cast_ofNat]
  have hs := Real.abs_log_sub_add_sum_range_le (show |(1 / 4 : ℝ)| < 1 by norm_num) 4
  rw [abs_le] at hs
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs hl3
  have l2 := Real.log_two_gt_d9
  norm_num at hI
  linarith [hs.1, hs.2]

end Work.Fidelity.MaxwellMutantsReject
