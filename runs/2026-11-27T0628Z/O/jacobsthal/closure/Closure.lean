import Mathlib
import Readings.Jacobsthal
import ComparatorChallenges.JacobsthalImproved

/-! # Target O, family O23 (Jacobsthal's function): closures (run 2026-11-27T0628Z).
Frozen statement taken with `type_of%`, never retyped: `erdos_970_iterated_log` — some C > 0 such that for
every k ≥ 1 some m has the Jacobsthal property for every n ≥ 1 with ω(n) ≤ k (every a + 0, …, a + m − 1
contains an integer coprime to n) and m ≤ C k² / (log log 3k)². Closed (frozen ⇒ reading): every reader's
Theorem 1.1 (their j(n) ≤ m because m is admissible, so their h(k) ≤ m), and every reader's quadratic form
(Jacobsthal's question) from the same frozen statement, with C' = C / (log log 3)², since log log 3k ≥ log log 3 > 0.
The family's second challenge (`JacobsthalQuadratic`) cannot be imported with this one (both declare
`IsJacobsthalBound`); it is replayed on its own line. -/

namespace TargetO.Jacobsthal

/-- The frozen statement, unpacked with `Int.gcd`. -/
theorem unpack (h : type_of% @OAI.Erdos970.Erdos970Final.erdos_970_iterated_log) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → ∃ m : ℕ, 0 < m ∧
      (∀ n : ℕ, 1 ≤ n → n.primeFactors.card ≤ k → ∀ a : ℤ, ∃ i : ℕ, i < m ∧ Int.gcd (a + i) n = 1) ∧
      (m : ℝ) ≤ C * (k : ℝ) ^ 2 / (Real.log (Real.log (3 * (k : ℝ)))) ^ 2 := by
  obtain ⟨C, hC, hk⟩ := h
  refine ⟨C, hC, fun k hk1 => ?_⟩
  obtain ⟨m, hm, hb⟩ := hk k hk1
  have hgood : ∀ n : ℕ, 1 ≤ n → n.primeFactors.card ≤ k → ∀ a : ℤ, ∃ i : ℕ, i < m ∧
      Int.gcd (a + i) n = 1 := by
    intro n hn hω a
    obtain ⟨i, hi, hc⟩ := hm n hn hω a
    exact ⟨i, hi, by simpa [Int.gcd] using hc⟩
  have hpos : 0 < m := by
    obtain ⟨i, hi, -⟩ := hgood 1 le_rfl (by simp) 0
    omega
  exact ⟨m, hpos, hgood, hb⟩

theorem loglog3_pos : 0 < Real.log (Real.log 3) := by
  apply Real.log_pos
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- The quadratic bound from the iterated-log one. -/
theorem quad {C : ℝ} (hC : 0 < C) {k : ℕ} (hk : 1 ≤ k) {m : ℝ}
    (hm : m ≤ C * (k : ℝ) ^ 2 / (Real.log (Real.log (3 * (k : ℝ)))) ^ 2) :
    m ≤ C / (Real.log (Real.log 3)) ^ 2 * (k : ℝ) ^ 2 := by
  have h3 : (3 : ℝ) ≤ 3 * k := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hl : Real.log (Real.log 3) ≤ Real.log (Real.log (3 * k)) := by
    apply Real.log_le_log (Real.log_pos (by norm_num))
    exact Real.log_le_log (by norm_num) h3
  have h0 := loglog3_pos
  refine hm.trans ?_
  rw [div_mul_eq_mul_div, mul_comm C]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  gcongr

theorem A_j_le {n m : ℕ} (hm : 0 < m)
    (hg : ∀ a : ℤ, ∃ i : ℕ, i < m ∧ Int.gcd (a + i) n = 1) : ReaderA.j n ≤ m := by
  apply Nat.sInf_le
  refine ⟨hm, fun a => ?_⟩
  obtain ⟨i, hi, hc⟩ := hg a
  refine ⟨a + i, by omega, by omega, ?_⟩
  rw [Int.isCoprime_iff_gcd_eq_one]; exact hc

theorem A_h_le {k m : ℕ} (hm : 0 < m)
    (hg : ∀ n : ℕ, 1 ≤ n → n.primeFactors.card ≤ k → ∀ a : ℤ, ∃ i : ℕ, i < m ∧ Int.gcd (a + i) n = 1) :
    ReaderA.h k ≤ (m : ENNReal) := by
  unfold ReaderA.h
  refine iSup₂_le fun n hn => ?_
  exact_mod_cast A_j_le hm (hg n hn.1 hn.2)

theorem A_thm : (type_of% @OAI.Erdos970.Erdos970Final.erdos_970_iterated_log) →
    (type_of% @ReaderA.reading_thm_1_1) := by
  intro h
  obtain ⟨C, hC, hk⟩ := unpack h
  refine ⟨C, hC, fun k hk1 => ?_⟩
  obtain ⟨m, hm, hg, hb⟩ := hk k hk1
  refine (A_h_le hm hg).trans ?_
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal hb

theorem A_quad : (type_of% @OAI.Erdos970.Erdos970Final.erdos_970_iterated_log) →
    (type_of% @ReaderA.reading_jacobsthal_question) := by
  intro h
  obtain ⟨C, hC, hk⟩ := unpack h
  refine ⟨C / (Real.log (Real.log 3)) ^ 2, by have := loglog3_pos; positivity, fun k hk1 => ?_⟩
  obtain ⟨m, hm, hg, hb⟩ := hk k hk1
  refine (A_h_le hm hg).trans ?_
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (quad hC hk1 hb)

theorem B_h_le {k m : ℕ} (hm : 0 < m)
    (hg : ∀ n : ℕ, 1 ≤ n → n.primeFactors.card ≤ k → ∀ a : ℤ, ∃ i : ℕ, i < m ∧ Int.gcd (a + i) n = 1) :
    ((ReaderB.h k : ℕ∞) : ENNReal) ≤ (m : ENNReal) := by
  have : ReaderB.h k ≤ (m : ℕ∞) := by
    unfold ReaderB.h
    refine iSup_le fun n => ?_
    have hj : ReaderB.j n.1 ≤ m := by
      apply Nat.sInf_le
      refine ⟨hm, fun a => ?_⟩
      obtain ⟨i, hi, hc⟩ := hg n.1 n.2.1 n.2.2 a
      exact ⟨i, hi, by rw [Int.isCoprime_iff_gcd_eq_one]; exact hc⟩
    exact_mod_cast hj
  calc ((ReaderB.h k : ℕ∞) : ENNReal) ≤ (((m : ℕ) : ℕ∞) : ENNReal) := ENat.toENNReal_le.mpr this
    _ = (m : ENNReal) := by simp

theorem B_thm : (type_of% @OAI.Erdos970.Erdos970Final.erdos_970_iterated_log) →
    (type_of% @ReaderB.reading_jacobsthal_main) := by
  intro h
  obtain ⟨C, hC, hk⟩ := unpack h
  refine ⟨C, hC, fun k hk1 => ?_⟩
  obtain ⟨m, hm, hg, hb⟩ := hk k hk1
  refine (B_h_le hm hg).trans ?_
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal hb

theorem B_quad : (type_of% @OAI.Erdos970.Erdos970Final.erdos_970_iterated_log) →
    (type_of% @ReaderB.reading_jacobsthal_quadratic) := by
  intro h
  obtain ⟨C, hC, hk⟩ := unpack h
  refine ⟨C / (Real.log (Real.log 3)) ^ 2, by have := loglog3_pos; positivity, fun k hk1 => ?_⟩
  obtain ⟨m, hm, hg, hb⟩ := hk k hk1
  refine (B_h_le hm hg).trans ?_
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (quad hC hk1 hb)

theorem C_h_le {k m : ℕ} (hm : 0 < m)
    (hg : ∀ n : ℕ, 1 ≤ n → n.primeFactors.card ≤ k → ∀ a : ℤ, ∃ i : ℕ, i < m ∧ Int.gcd (a + i) n = 1) :
    ENat.toENNReal (ReaderC.hJac k) ≤ (m : ENNReal) := by
  have : ReaderC.hJac k ≤ (m : ℕ∞) := by
    unfold ReaderC.hJac
    refine iSup₂_le fun n hn => ?_
    unfold ReaderC.jac
    exact iInf₂_le m ⟨hm, hg n hn.1 hn.2⟩
  calc ENat.toENNReal (ReaderC.hJac k) ≤ ENat.toENNReal ((m : ℕ) : ℕ∞) := ENat.toENNReal_le.mpr this
    _ = (m : ENNReal) := by simp

theorem C_thm : (type_of% @OAI.Erdos970.Erdos970Final.erdos_970_iterated_log) →
    (type_of% @ReaderC.reading_jacobsthal_main) := by
  intro h
  obtain ⟨C, hC, hk⟩ := unpack h
  refine ⟨C, hC, fun k hk1 => ?_⟩
  obtain ⟨m, hm, hg, hb⟩ := hk k hk1
  refine (C_h_le hm hg).trans ?_
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal hb

theorem C_quad : (type_of% @OAI.Erdos970.Erdos970Final.erdos_970_iterated_log) →
    (type_of% @ReaderC.reading_jacobsthal_erdos_question) := by
  intro h
  obtain ⟨C, hC, hk⟩ := unpack h
  refine ⟨C / (Real.log (Real.log 3)) ^ 2, by have := loglog3_pos; positivity, fun k hk1 => ?_⟩
  obtain ⟨m, hm, hg, hb⟩ := hk k hk1
  refine (C_h_le hm hg).trans ?_
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (quad hC hk1 hb)

end TargetO.Jacobsthal

#print axioms TargetO.Jacobsthal.A_thm
#print axioms TargetO.Jacobsthal.A_quad
#print axioms TargetO.Jacobsthal.B_thm
#print axioms TargetO.Jacobsthal.B_quad
#print axioms TargetO.Jacobsthal.C_thm
#print axioms TargetO.Jacobsthal.C_quad
