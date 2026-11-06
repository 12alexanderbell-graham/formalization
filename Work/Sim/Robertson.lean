import Mathlib
import Work.Sim.RobCerts4

/-!
# Robertson's stiff reaction network: certified state at t = 40 (FROZEN statements)

THE RESULT part 1 ("rigorous simulators"), first stiff system. Robertson's (1966) network
A → B (rate constant k₁), B + C → A + C (k₂), 2B → B + C (k₃), with mass-action rate
equations for the concentrations y₁ = [A], y₂ = [B], y₃ = [C]:
y₁′ = −k₁ y₁ + k₂ y₂ y₃, y₂′ = k₁ y₁ − k₂ y₂ y₃ − k₃ y₂², y₃′ = k₃ y₂².
The standard stiff test problem takes k₁ = 0.04, k₂ = 10⁴, k₃ = 3·10⁷ and y(0) = (1, 0, 0).
The Jacobian has a stiff eigenvalue of size ≈ 2–3·10³ for most of [0, 40] (referee of run
2026-11-06T0428Z; ≈ −3.4·10³ at t = 40) against a slow one of size ≲ 1, so a classical Grönwall
enclosure (growth e^{Lt} with the full Lipschitz constant) is useless; the proof uses the
one-sided (logarithmic-norm) cell step `Work.Sim.OneSided.onesided_cell` in the weighted norm
4900·e₂² + e₃², in which the network is almost non-expanding.

Statements are about *every* solution of the rate equations on [0, 40] (derivatives within the
interval); existence is a separate statement.
-/

namespace Work.Sim.Robertson
open Set

/-- `IsRobSolution k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃`: the concentrations y₁ = [A], y₂ = [B],
y₃ = [C] solve the mass-action rate equations of Robertson's network A → B (k₁),
B + C → A + C (k₂), 2B → B + C (k₃) on the time interval [0, T]: initial values a₀, b₀, c₀ at
t = 0, and at every t ∈ [0, T] derivatives within [0, T]
y₁′ = −k₁ y₁ + k₂ y₂ y₃, y₂′ = k₁ y₁ − k₂ y₂ y₃ − k₃ y₂², y₃′ = k₃ y₂². -/
def IsRobSolution (k₁ k₂ k₃ a₀ b₀ c₀ T : ℝ) (y₁ y₂ y₃ : ℝ → ℝ) : Prop :=
  y₁ 0 = a₀ ∧ y₂ 0 = b₀ ∧ y₃ 0 = c₀ ∧ ∀ t ∈ Icc 0 T,
    HasDerivWithinAt y₁ (-k₁ * y₁ t + k₂ * y₂ t * y₃ t) (Icc 0 T) t ∧
    HasDerivWithinAt y₂ (k₁ * y₁ t - k₂ * y₂ t * y₃ t - k₃ * y₂ t ^ 2) (Icc 0 T) t ∧
    HasDerivWithinAt y₃ (k₃ * y₂ t ^ 2) (Icc 0 T) t

/-- A function with zero derivative within [0, T] at every point of [0, T] is constant there. -/
theorem const_of_zero {F : ℝ → ℝ} {T : ℝ}
    (hF : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt F 0 (Icc 0 T) t) :
    ∀ t ∈ Icc (0 : ℝ) T, F t = F 0 :=
  constant_of_has_deriv_right_zero (fun t ht => (hF t ht).continuousWithinAt)
    (fun t ht => (hF t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))

/-- Reduction to the (y₂, y₃) system by conservation of y₁ + y₂ + y₃, then the 49 generated
cells of `Work.Sim.RobCerts`. -/
theorem enclosure40 {y₁ y₂ y₃ : ℝ → ℝ}
    (h : IsRobSolution (1 / 25) 10000 30000000 1 0 0 40 y₁ y₂ y₃) :
    4900 * (y₂ 40 - (4592767382278885557 / 500000000000000000000000 : ℝ)) ^ 2 + (y₃ 40 - (2841637457458304589 / 10000000000000000000 : ℝ)) ^ 2 ≤ (183 / 100000000000 : ℝ) ^ 2 ∧
      ∀ t ∈ Icc (0 : ℝ) 40, y₁ t = 1 - y₂ t - y₃ t := by
  obtain ⟨h1, h2, h3, hd⟩ := h
  have hM := const_of_zero (F := fun t => y₁ t + y₂ t + y₃ t) (T := 40) (fun t ht => by
      have := ((hd t ht).1.add (hd t ht).2.1).add (hd t ht).2.2
      convert this using 1; ring)
  have hy1 : ∀ t ∈ Icc (0 : ℝ) 40, y₁ t = 1 - y₂ t - y₃ t := fun t ht => by
    have := hM t ht; simp only [h1, h2, h3] at this; linarith
  have hd2 : ∀ t ∈ Icc (0 : ℝ) 40, HasDerivWithinAt y₂
      (Work.Sim.RobCell.robP (y₂ t) (y₃ t)) (Icc 0 40) t := fun t ht => by
    have := (hd t ht).2.1
    convert this using 1
    rw [hy1 t ht]; unfold Work.Sim.RobCell.robP; ring
  have hd3 : ∀ t ∈ Icc (0 : ℝ) 40, HasDerivWithinAt y₃
      (Work.Sim.RobCell.robQ (y₂ t) (y₃ t)) (Icc 0 40) t := fun t ht => by
    have := (hd t ht).2.2
    convert this using 1
    unfold Work.Sim.RobCell.robQ; ring
  have hP : ∀ a b : ℝ, -1 / 1000 ≤ a → a ≤ 1 / 1000 → -1 / 10 ≤ b → b ≤ 11 / 10 →
      Work.Sim.RobCell.robP a b = Work.Sim.RobCell.robP a b ∧
        Work.Sim.RobCell.robQ a b = Work.Sim.RobCell.robQ a b :=
    fun _ _ _ _ _ _ => ⟨rfl, rfl⟩
  have s0 : 4900 * (y₂ (0 : ℝ) - (0 : ℝ)) ^ 2 + (y₃ (0 : ℝ) - (0 : ℝ)) ^ 2 ≤ (0 : ℝ) ^ 2 := by
    simp [h2, h3]
  refine ⟨?_, hy1⟩
  have c0 := Work.Sim.RobCerts.step0 hP hd2 hd3 s0
  have c1 := Work.Sim.RobCerts.step1 hP hd2 hd3 c0
  have c2 := Work.Sim.RobCerts.step2 hP hd2 hd3 c1
  have c3 := Work.Sim.RobCerts.step3 hP hd2 hd3 c2
  have c4 := Work.Sim.RobCerts.step4 hP hd2 hd3 c3
  have c5 := Work.Sim.RobCerts.step5 hP hd2 hd3 c4
  have c6 := Work.Sim.RobCerts.step6 hP hd2 hd3 c5
  have c7 := Work.Sim.RobCerts.step7 hP hd2 hd3 c6
  have c8 := Work.Sim.RobCerts.step8 hP hd2 hd3 c7
  have c9 := Work.Sim.RobCerts.step9 hP hd2 hd3 c8
  have c10 := Work.Sim.RobCerts.step10 hP hd2 hd3 c9
  have c11 := Work.Sim.RobCerts.step11 hP hd2 hd3 c10
  have c12 := Work.Sim.RobCerts.step12 hP hd2 hd3 c11
  have c13 := Work.Sim.RobCerts.step13 hP hd2 hd3 c12
  have c14 := Work.Sim.RobCerts.step14 hP hd2 hd3 c13
  have c15 := Work.Sim.RobCerts.step15 hP hd2 hd3 c14
  have c16 := Work.Sim.RobCerts.step16 hP hd2 hd3 c15
  have c17 := Work.Sim.RobCerts.step17 hP hd2 hd3 c16
  have c18 := Work.Sim.RobCerts.step18 hP hd2 hd3 c17
  have c19 := Work.Sim.RobCerts.step19 hP hd2 hd3 c18
  have c20 := Work.Sim.RobCerts.step20 hP hd2 hd3 c19
  have c21 := Work.Sim.RobCerts.step21 hP hd2 hd3 c20
  have c22 := Work.Sim.RobCerts.step22 hP hd2 hd3 c21
  have c23 := Work.Sim.RobCerts.step23 hP hd2 hd3 c22
  have c24 := Work.Sim.RobCerts.step24 hP hd2 hd3 c23
  have c25 := Work.Sim.RobCerts.step25 hP hd2 hd3 c24
  have c26 := Work.Sim.RobCerts.step26 hP hd2 hd3 c25
  have c27 := Work.Sim.RobCerts.step27 hP hd2 hd3 c26
  have c28 := Work.Sim.RobCerts.step28 hP hd2 hd3 c27
  have c29 := Work.Sim.RobCerts.step29 hP hd2 hd3 c28
  have c30 := Work.Sim.RobCerts.step30 hP hd2 hd3 c29
  have c31 := Work.Sim.RobCerts.step31 hP hd2 hd3 c30
  have c32 := Work.Sim.RobCerts.step32 hP hd2 hd3 c31
  have c33 := Work.Sim.RobCerts.step33 hP hd2 hd3 c32
  have c34 := Work.Sim.RobCerts.step34 hP hd2 hd3 c33
  have c35 := Work.Sim.RobCerts.step35 hP hd2 hd3 c34
  have c36 := Work.Sim.RobCerts.step36 hP hd2 hd3 c35
  have c37 := Work.Sim.RobCerts.step37 hP hd2 hd3 c36
  have c38 := Work.Sim.RobCerts.step38 hP hd2 hd3 c37
  have c39 := Work.Sim.RobCerts.step39 hP hd2 hd3 c38
  have c40 := Work.Sim.RobCerts.step40 hP hd2 hd3 c39
  have c41 := Work.Sim.RobCerts.step41 hP hd2 hd3 c40
  have c42 := Work.Sim.RobCerts.step42 hP hd2 hd3 c41
  have c43 := Work.Sim.RobCerts.step43 hP hd2 hd3 c42
  have c44 := Work.Sim.RobCerts.step44 hP hd2 hd3 c43
  have c45 := Work.Sim.RobCerts.step45 hP hd2 hd3 c44
  have c46 := Work.Sim.RobCerts.step46 hP hd2 hd3 c45
  have c47 := Work.Sim.RobCerts.step47 hP hd2 hd3 c46
  have c48 := Work.Sim.RobCerts.step48 hP hd2 hd3 c47
  exact c48

/-- Certified state of Robertson's stiff network at t = 40: for k₁ = 1/25, k₂ = 10⁴,
k₃ = 3·10⁷ and initial concentrations (1, 0, 0), every solution of the rate equations on
[0, 40] has 0.7158270 < y₁(40) < 0.7158271, 9.1855·10⁻⁶ < y₂(40) < 9.1856·10⁻⁶ and
0.2841637 < y₃(40) < 0.2841638. -/
theorem rob_state40 {y₁ y₂ y₃ : ℝ → ℝ}
    (h : IsRobSolution (1 / 25) 10000 30000000 1 0 0 40 y₁ y₂ y₃) :
    7158270 / 10000000 < y₁ 40 ∧ y₁ 40 < 7158271 / 10000000 ∧
    91855 / 10000000000 < y₂ 40 ∧ y₂ 40 < 91856 / 10000000000 ∧
    2841637 / 10000000 < y₃ 40 ∧ y₃ 40 < 2841638 / 10000000 := by
  obtain ⟨he, hy1⟩ := enclosure40 h
  have q2 : (70 * (y₂ 40 - (4592767382278885557 / 500000000000000000000000 : ℝ))) ^ 2 ≤ (183 / 100000000000 : ℝ) ^ 2 := by nlinarith [sq_nonneg (y₃ 40 - (2841637457458304589 / 10000000000000000000 : ℝ))]
  have q3 : (y₃ 40 - (2841637457458304589 / 10000000000000000000 : ℝ)) ^ 2 ≤ (183 / 100000000000 : ℝ) ^ 2 := by nlinarith [sq_nonneg (y₂ 40 - (4592767382278885557 / 500000000000000000000000 : ℝ))]
  have a2 := abs_le.1 (Work.Sim.RobCell.abs_le_of_sq (by norm_num) q2)
  have a3 := abs_le.1 (Work.Sim.RobCell.abs_le_of_sq (by norm_num) q3)
  have e1 := hy1 40 ⟨by norm_num, le_rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num at a2 a3 ⊢ <;> linarith [a2.1, a2.2, a3.1, a3.2]

/-- Robertson's network with k₁ = 1/25, k₂ = 10⁴, k₃ = 3·10⁷ and initial concentrations
(1, 0, 0) has a solution of the rate equations on [0, 40]. -/
theorem rob_exists : ∃ y₁ y₂ y₃ : ℝ → ℝ,
    IsRobSolution (1 / 25) 10000 30000000 1 0 0 40 y₁ y₂ y₃ := by
  sorry

end Work.Sim.Robertson
