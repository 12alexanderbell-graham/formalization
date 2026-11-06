import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Bound
import Checked.Sim.RobCerts4
import Checked.Sim.RobExists

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
one-sided (logarithmic-norm) cell step `Checked.Sim.OneSided.onesided_cell` in the weighted norm
4900·e₂² + e₃², in which the network is almost non-expanding.

Statements are about *every* solution of the rate equations on [0, 40] (derivatives within the
interval); existence is a separate statement.
-/

namespace Checked.Sim.Robertson
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

theorem fstW {α : ℝ → ℝ × ℝ} {d : ℝ × ℝ} {S : Set ℝ} {t : ℝ} (h : HasDerivWithinAt α d S t) :
    HasDerivWithinAt (fun s => (α s).1) d.1 S t := by
  have := h.hasFDerivWithinAt.fst.hasDerivWithinAt
  simpa using this

theorem sndW {α : ℝ → ℝ × ℝ} {d : ℝ × ℝ} {S : Set ℝ} {t : ℝ} (h : HasDerivWithinAt α d S t) :
    HasDerivWithinAt (fun s => (α s).2) d.2 S t := by
  have := h.hasFDerivWithinAt.snd.hasDerivWithinAt
  simpa using this

/-- The 49 generated cells of `Checked.Sim.RobCerts` chained, for any field equal to the reduced
Robertson field on the box: the solution stays in the box on [0, 40] and ends in the final
weighted ball. -/
theorem chain {P Q : ℝ → ℝ → ℝ}
    (hP : ∀ y2 y3, -1 / 1000 ≤ y2 → y2 ≤ 1 / 1000 → -1 / 10 ≤ y3 → y3 ≤ 11 / 10 →
      P y2 y3 = Checked.Sim.RobCell.robP y2 y3 ∧ Q y2 y3 = Checked.Sim.RobCell.robQ y2 y3)
    {y2 y3 : ℝ → ℝ}
    (hd2 : ∀ t ∈ Icc (0 : ℝ) 40, HasDerivWithinAt y2 (P (y2 t) (y3 t)) (Icc 0 40) t)
    (hd3 : ∀ t ∈ Icc (0 : ℝ) 40, HasDerivWithinAt y3 (Q (y2 t) (y3 t)) (Icc 0 40) t)
    (h20 : y2 0 = 0) (h30 : y3 0 = 0) :
    (∀ t ∈ Icc (0 : ℝ) 40, -1 / 1000 ≤ y2 t ∧ y2 t ≤ 1 / 1000 ∧ -1 / 10 ≤ y3 t ∧ y3 t ≤ 11 / 10) ∧
    4900 * (y2 40 - (4592767382278885557 / 500000000000000000000000 : ℝ)) ^ 2 + (y3 40 - (2841637457458304589 / 10000000000000000000 : ℝ)) ^ 2 ≤ (183 / 100000000000 : ℝ) ^ 2 := by
  have s0 : 4900 * (y2 (0 : ℝ) - (0 : ℝ)) ^ 2 + (y3 (0 : ℝ) - (0 : ℝ)) ^ 2 ≤ (0 : ℝ) ^ 2 := by
    simp [h20, h30]
  have c0 := Checked.Sim.RobCerts.step0 hP hd2 hd3 s0
  have c1 := Checked.Sim.RobCerts.step1 hP hd2 hd3 c0.2
  have c2 := Checked.Sim.RobCerts.step2 hP hd2 hd3 c1.2
  have c3 := Checked.Sim.RobCerts.step3 hP hd2 hd3 c2.2
  have c4 := Checked.Sim.RobCerts.step4 hP hd2 hd3 c3.2
  have c5 := Checked.Sim.RobCerts.step5 hP hd2 hd3 c4.2
  have c6 := Checked.Sim.RobCerts.step6 hP hd2 hd3 c5.2
  have c7 := Checked.Sim.RobCerts.step7 hP hd2 hd3 c6.2
  have c8 := Checked.Sim.RobCerts.step8 hP hd2 hd3 c7.2
  have c9 := Checked.Sim.RobCerts.step9 hP hd2 hd3 c8.2
  have c10 := Checked.Sim.RobCerts.step10 hP hd2 hd3 c9.2
  have c11 := Checked.Sim.RobCerts.step11 hP hd2 hd3 c10.2
  have c12 := Checked.Sim.RobCerts.step12 hP hd2 hd3 c11.2
  have c13 := Checked.Sim.RobCerts.step13 hP hd2 hd3 c12.2
  have c14 := Checked.Sim.RobCerts.step14 hP hd2 hd3 c13.2
  have c15 := Checked.Sim.RobCerts.step15 hP hd2 hd3 c14.2
  have c16 := Checked.Sim.RobCerts.step16 hP hd2 hd3 c15.2
  have c17 := Checked.Sim.RobCerts.step17 hP hd2 hd3 c16.2
  have c18 := Checked.Sim.RobCerts.step18 hP hd2 hd3 c17.2
  have c19 := Checked.Sim.RobCerts.step19 hP hd2 hd3 c18.2
  have c20 := Checked.Sim.RobCerts.step20 hP hd2 hd3 c19.2
  have c21 := Checked.Sim.RobCerts.step21 hP hd2 hd3 c20.2
  have c22 := Checked.Sim.RobCerts.step22 hP hd2 hd3 c21.2
  have c23 := Checked.Sim.RobCerts.step23 hP hd2 hd3 c22.2
  have c24 := Checked.Sim.RobCerts.step24 hP hd2 hd3 c23.2
  have c25 := Checked.Sim.RobCerts.step25 hP hd2 hd3 c24.2
  have c26 := Checked.Sim.RobCerts.step26 hP hd2 hd3 c25.2
  have c27 := Checked.Sim.RobCerts.step27 hP hd2 hd3 c26.2
  have c28 := Checked.Sim.RobCerts.step28 hP hd2 hd3 c27.2
  have c29 := Checked.Sim.RobCerts.step29 hP hd2 hd3 c28.2
  have c30 := Checked.Sim.RobCerts.step30 hP hd2 hd3 c29.2
  have c31 := Checked.Sim.RobCerts.step31 hP hd2 hd3 c30.2
  have c32 := Checked.Sim.RobCerts.step32 hP hd2 hd3 c31.2
  have c33 := Checked.Sim.RobCerts.step33 hP hd2 hd3 c32.2
  have c34 := Checked.Sim.RobCerts.step34 hP hd2 hd3 c33.2
  have c35 := Checked.Sim.RobCerts.step35 hP hd2 hd3 c34.2
  have c36 := Checked.Sim.RobCerts.step36 hP hd2 hd3 c35.2
  have c37 := Checked.Sim.RobCerts.step37 hP hd2 hd3 c36.2
  have c38 := Checked.Sim.RobCerts.step38 hP hd2 hd3 c37.2
  have c39 := Checked.Sim.RobCerts.step39 hP hd2 hd3 c38.2
  have c40 := Checked.Sim.RobCerts.step40 hP hd2 hd3 c39.2
  have c41 := Checked.Sim.RobCerts.step41 hP hd2 hd3 c40.2
  have c42 := Checked.Sim.RobCerts.step42 hP hd2 hd3 c41.2
  have c43 := Checked.Sim.RobCerts.step43 hP hd2 hd3 c42.2
  have c44 := Checked.Sim.RobCerts.step44 hP hd2 hd3 c43.2
  have c45 := Checked.Sim.RobCerts.step45 hP hd2 hd3 c44.2
  have c46 := Checked.Sim.RobCerts.step46 hP hd2 hd3 c45.2
  have c47 := Checked.Sim.RobCerts.step47 hP hd2 hd3 c46.2
  have c48 := Checked.Sim.RobCerts.step48 hP hd2 hd3 c47.2
  refine ⟨fun t ht => ?_, c48.2⟩
  rcases le_or_gt t (1 / 100000 : ℝ) with g0 | g0
  · exact c0.1 t ⟨ht.1, g0⟩
  rcases le_or_gt t (1 / 40000 : ℝ) with g1 | g1
  · exact c1.1 t ⟨g0.le, g1⟩
  rcases le_or_gt t (47 / 1000000 : ℝ) with g2 | g2
  · exact c2.1 t ⟨g1.le, g2⟩
  rcases le_or_gt t (1 / 12500 : ℝ) with g3 | g3
  · exact c3.1 t ⟨g2.le, g3⟩
  rcases le_or_gt t (129 / 1000000 : ℝ) with g4 | g4
  · exact c4.1 t ⟨g3.le, g4⟩
  rcases le_or_gt t (101 / 500000 : ℝ) with g5 | g5
  · exact c5.1 t ⟨g4.le, g5⟩
  rcases le_or_gt t (39 / 125000 : ℝ) with g6 | g6
  · exact c6.1 t ⟨g5.le, g6⟩
  rcases le_or_gt t (59 / 125000 : ℝ) with g7 | g7
  · exact c7.1 t ⟨g6.le, g7⟩
  rcases le_or_gt t (89 / 125000 : ℝ) with g8 | g8
  · exact c8.1 t ⟨g7.le, g8⟩
  rcases le_or_gt t (67 / 62500 : ℝ) with g9 | g9
  · exact c9.1 t ⟨g8.le, g9⟩
  rcases le_or_gt t (403 / 250000 : ℝ) with g10 | g10
  · exact c10.1 t ⟨g9.le, g10⟩
  rcases le_or_gt t (1211 / 500000 : ℝ) with g11 | g11
  · exact c11.1 t ⟨g10.le, g11⟩
  rcases le_or_gt t (1811 / 500000 : ℝ) with g12 | g12
  · exact c12.1 t ⟨g11.le, g12⟩
  rcases le_or_gt t (2711 / 500000 : ℝ) with g13 | g13
  · exact c13.1 t ⟨g12.le, g13⟩
  rcases le_or_gt t (4061 / 500000 : ℝ) with g14 | g14
  · exact c14.1 t ⟨g13.le, g14⟩
  rcases le_or_gt t (6061 / 500000 : ℝ) with g15 | g15
  · exact c15.1 t ⟨g14.le, g15⟩
  rcases le_or_gt t (9061 / 500000 : ℝ) with g16 | g16
  · exact c16.1 t ⟨g15.le, g16⟩
  rcases le_or_gt t (13561 / 500000 : ℝ) with g17 | g17
  · exact c17.1 t ⟨g16.le, g17⟩
  rcases le_or_gt t (20061 / 500000 : ℝ) with g18 | g18
  · exact c18.1 t ⟨g17.le, g18⟩
  rcases le_or_gt t (30061 / 500000 : ℝ) with g19 | g19
  · exact c19.1 t ⟨g18.le, g19⟩
  rcases le_or_gt t (45061 / 500000 : ℝ) with g20 | g20
  · exact c20.1 t ⟨g19.le, g20⟩
  rcases le_or_gt t (67561 / 500000 : ℝ) with g21 | g21
  · exact c21.1 t ⟨g20.le, g21⟩
  rcases le_or_gt t (101561 / 500000 : ℝ) with g22 | g22
  · exact c22.1 t ⟨g21.le, g22⟩
  rcases le_or_gt t (151561 / 500000 : ℝ) with g23 | g23
  · exact c23.1 t ⟨g22.le, g23⟩
  rcases le_or_gt t (226561 / 500000 : ℝ) with g24 | g24
  · exact c24.1 t ⟨g23.le, g24⟩
  rcases le_or_gt t (336561 / 500000 : ℝ) with g25 | g25
  · exact c25.1 t ⟨g24.le, g25⟩
  rcases le_or_gt t (501561 / 500000 : ℝ) with g26 | g26
  · exact c26.1 t ⟨g25.le, g26⟩
  rcases le_or_gt t (746561 / 500000 : ℝ) with g27 | g27
  · exact c27.1 t ⟨g26.le, g27⟩
  rcases le_or_gt t (1116561 / 500000 : ℝ) with g28 | g28
  · exact c28.1 t ⟨g27.le, g28⟩
  rcases le_or_gt t (1666561 / 500000 : ℝ) with g29 | g29
  · exact c29.1 t ⟨g28.le, g29⟩
  rcases le_or_gt t (2466561 / 500000 : ℝ) with g30 | g30
  · exact c30.1 t ⟨g29.le, g30⟩
  rcases le_or_gt t (3466561 / 500000 : ℝ) with g31 | g31
  · exact c31.1 t ⟨g30.le, g31⟩
  rcases le_or_gt t (4466561 / 500000 : ℝ) with g32 | g32
  · exact c32.1 t ⟨g31.le, g32⟩
  rcases le_or_gt t (5466561 / 500000 : ℝ) with g33 | g33
  · exact c33.1 t ⟨g32.le, g33⟩
  rcases le_or_gt t (6466561 / 500000 : ℝ) with g34 | g34
  · exact c34.1 t ⟨g33.le, g34⟩
  rcases le_or_gt t (7466561 / 500000 : ℝ) with g35 | g35
  · exact c35.1 t ⟨g34.le, g35⟩
  rcases le_or_gt t (8466561 / 500000 : ℝ) with g36 | g36
  · exact c36.1 t ⟨g35.le, g36⟩
  rcases le_or_gt t (9466561 / 500000 : ℝ) with g37 | g37
  · exact c37.1 t ⟨g36.le, g37⟩
  rcases le_or_gt t (10466561 / 500000 : ℝ) with g38 | g38
  · exact c38.1 t ⟨g37.le, g38⟩
  rcases le_or_gt t (11466561 / 500000 : ℝ) with g39 | g39
  · exact c39.1 t ⟨g38.le, g39⟩
  rcases le_or_gt t (12466561 / 500000 : ℝ) with g40 | g40
  · exact c40.1 t ⟨g39.le, g40⟩
  rcases le_or_gt t (13466561 / 500000 : ℝ) with g41 | g41
  · exact c41.1 t ⟨g40.le, g41⟩
  rcases le_or_gt t (14466561 / 500000 : ℝ) with g42 | g42
  · exact c42.1 t ⟨g41.le, g42⟩
  rcases le_or_gt t (15466561 / 500000 : ℝ) with g43 | g43
  · exact c43.1 t ⟨g42.le, g43⟩
  rcases le_or_gt t (16466561 / 500000 : ℝ) with g44 | g44
  · exact c44.1 t ⟨g43.le, g44⟩
  rcases le_or_gt t (17466561 / 500000 : ℝ) with g45 | g45
  · exact c45.1 t ⟨g44.le, g45⟩
  rcases le_or_gt t (18466561 / 500000 : ℝ) with g46 | g46
  · exact c46.1 t ⟨g45.le, g46⟩
  rcases le_or_gt t (19466561 / 500000 : ℝ) with g47 | g47
  · exact c47.1 t ⟨g46.le, g47⟩
  exact c48.1 t ⟨g47.le, ht.2⟩

/-- Reduction to the (y₂, y₃) system by conservation of y₁ + y₂ + y₃, then `chain`. -/
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
      (Checked.Sim.RobCell.robP (y₂ t) (y₃ t)) (Icc 0 40) t := fun t ht => by
    have := (hd t ht).2.1
    convert this using 1
    rw [hy1 t ht]; unfold Checked.Sim.RobCell.robP; ring
  have hd3 : ∀ t ∈ Icc (0 : ℝ) 40, HasDerivWithinAt y₃
      (Checked.Sim.RobCell.robQ (y₂ t) (y₃ t)) (Icc 0 40) t := fun t ht => by
    have := (hd t ht).2.2
    convert this using 1
    unfold Checked.Sim.RobCell.robQ; ring
  exact ⟨(chain (fun _ _ _ _ _ _ => ⟨rfl, rfl⟩) hd2 hd3 h2 h3).2, hy1⟩

/-- The clamped field equals the reduced Robertson field on the box. -/
theorem Φc_eq (a b : ℝ) (h1 : -1 / 1000 ≤ a) (h2 : a ≤ 1 / 1000) (h3 : -1 / 10 ≤ b)
    (h4 : b ≤ 11 / 10) :
    (Checked.Sim.RobExists.Φc (a, b)).1 = Checked.Sim.RobCell.robP a b ∧
      (Checked.Sim.RobExists.Φc (a, b)).2 = Checked.Sim.RobCell.robQ a b := by
  have e1 : Checked.Sim.RobExists.cl (-1/1000) (1/1000) a = a := Checked.Sim.RobExists.cl_of_mem h1 h2
  have e2 : Checked.Sim.RobExists.cl (-1/10) (11/10) b = b := Checked.Sim.RobExists.cl_of_mem h3 h4
  simp only [Checked.Sim.RobExists.Φc, e1, e2, Checked.Sim.RobCell.robP, Checked.Sim.RobCell.robQ]
  constructor <;> first | trivial | ring

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
  have a2 := abs_le.1 (Checked.Sim.RobCell.abs_le_of_sq (by norm_num) q2)
  have a3 := abs_le.1 (Checked.Sim.RobCell.abs_le_of_sq (by norm_num) q3)
  have e1 := hy1 40 ⟨by norm_num, le_rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num at a2 a3 ⊢ <;> linarith [a2.1, a2.2, a3.1, a3.2]

/-- Robertson's network with k₁ = 1/25, k₂ = 10⁴, k₃ = 3·10⁷ and initial concentrations
(1, 0, 0) has a solution of the rate equations on [0, 40]. -/
theorem rob_exists : ∃ y₁ y₂ y₃ : ℝ → ℝ,
    IsRobSolution (1 / 25) 10000 30000000 1 0 0 40 y₁ y₂ y₃ := by
  obtain ⟨α, h0, hα⟩ := Checked.Sim.RobExists.exists_clamped
  have hd2 : ∀ t ∈ Icc (0 : ℝ) 40, HasDerivWithinAt (fun s => (α s).1)
      ((fun a b => (Checked.Sim.RobExists.Φc (a, b)).1) ((α t).1) ((α t).2)) (Icc 0 40) t :=
    fun t ht => by simpa using fstW (hα t ht)
  have hd3 : ∀ t ∈ Icc (0 : ℝ) 40, HasDerivWithinAt (fun s => (α s).2)
      ((fun a b => (Checked.Sim.RobExists.Φc (a, b)).2) ((α t).1) ((α t).2)) (Icc 0 40) t :=
    fun t ht => by simpa using sndW (hα t ht)
  obtain ⟨hbox, -⟩ := chain (P := fun a b => (Checked.Sim.RobExists.Φc (a, b)).1)
    (Q := fun a b => (Checked.Sim.RobExists.Φc (a, b)).2) Φc_eq hd2 hd3 (by simp [h0]) (by simp [h0])
  refine ⟨fun t => 1 - (α t).1 - (α t).2, fun t => (α t).1, fun t => (α t).2,
    by simp [h0], by simp [h0], by simp [h0], fun t ht => ?_⟩
  obtain ⟨b1, b2, b3, b4⟩ := hbox t ht
  obtain ⟨e1, e2⟩ := Φc_eq _ _ b1 b2 b3 b4
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

end Checked.Sim.Robertson
