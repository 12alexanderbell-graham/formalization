import ComparatorChallenges.QuantitativeVanDerWaerden
import Readings.Vdw

/-! Closure of the blind reading (runs/2026-11-26T1529Z/S/vdw/reading.lean) against the frozen
comparator statement `OAI.QuantitativeVanDerWaerden.uniform_lower_bound` (family 160, Erdős's
superexponential van der Waerden question). Statements taken with `type_of%`, never retyped.

The reading asserts that `W_r(k)` exists for every `k ≥ 1` (no junk `sInf`); the frozen statement
does not prove finiteness for small `k`. Finiteness is proved here from Mathlib's Hales–Jewett
theorem (`vdw_finite`), so the closure needs nothing beyond the frozen statement and Mathlib. -/

namespace ExternalS.Vdw
open OAI.QuantitativeVanDerWaerden Filter Combinatorics

/-- Finite van der Waerden theorem in the frozen statement's encoding, from Hales–Jewett. -/
theorem vdw_finite (r k : ℕ) (hk : 1 ≤ k) : ∃ N, 0 < N ∧ IsRamsey (Fin r) k N := by
  classical
  obtain ⟨ι, _, hι⟩ := Line.exists_mono_in_high_dimension (Fin k) (Fin r)
  refine ⟨Fintype.card ι * k + 1, Nat.succ_pos _, fun c => ?_⟩
  obtain ⟨l, col, hl⟩ := hι (fun v => c (∑ i, (v i : ℕ)))
  set s : Finset ι := Finset.univ.filter (fun i => l.idxFun i = none) with hs
  have hlin : ∀ x : Fin k, (∑ i, (l x i : ℕ)) = (∑ i, (l ⟨0, hk⟩ i : ℕ)) + s.card * x := by
    intro x
    rw [Finset.card_eq_sum_ones, Finset.sum_mul, one_mul, hs, Finset.sum_filter,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    simp only [Line.coe_apply]
    cases h : l.idxFun i <;> simp
  have hpos : 0 < s.card :=
    Finset.card_pos.mpr ⟨l.proper.choose, by simp [hs, l.proper.choose_spec]⟩
  refine ⟨∑ i, (l ⟨0, hk⟩ i : ℕ), s.card, hpos, ?_, ?_⟩
  · have hk1 : k - 1 < k := by omega
    calc (∑ i, (l ⟨0, hk⟩ i : ℕ)) + (k - 1) * s.card = ∑ i, (l ⟨k - 1, hk1⟩ i : ℕ) := by
          rw [hlin ⟨k - 1, hk1⟩, mul_comm]
      _ ≤ ∑ _i : ι, (k - 1) :=
          Finset.sum_le_sum (fun i _ => by have := (l ⟨k - 1, hk1⟩ i).isLt; omega)
      _ = Fintype.card ι * (k - 1) := by simp
      _ < Fintype.card ι * k + 1 := by
          have := Nat.mul_le_mul_left (Fintype.card ι) (Nat.sub_le k 1); omega
  · intro j hj
    have h1 : c (∑ i, (l ⟨j, hj⟩ i : ℕ)) = col := hl _
    have h0 : c (∑ i, (l ⟨0, hk⟩ i : ℕ)) = col := hl _
    rw [hlin ⟨j, hj⟩, mul_comm] at h1
    exact h1.trans h0.symm

/-- For `k ≥ 1` the reader's `[N] = {1,…,N}` encoding and the frozen `{0,…,N-1}` encoding agree. -/
lemma good_iff (r k N : ℕ) (hk : 1 ≤ k) :
    BlindVdw.GoodN r k N ↔ (0 < N ∧ IsRamsey (Fin r) k N) := by
  constructor
  · rintro ⟨hN, h⟩
    refine ⟨hN, fun c => ?_⟩
    obtain ⟨a, d, ha, hd, hle, hmono⟩ := h (fun x => c (x - 1))
    refine ⟨a - 1, d, hd, ?_, fun j hj => ?_⟩
    · have := hle (k - 1) (by omega); omega
    · have := hmono j hj
      have e1 : a + j * d - 1 = a - 1 + j * d := by omega
      simpa [e1] using this
  · rintro ⟨hN, h⟩
    refine ⟨hN, fun f => ?_⟩
    obtain ⟨a, d, hd, hlt, hmono⟩ := h (fun x => f (x + 1))
    refine ⟨a + 1, d, by omega, hd, fun i hi => ?_, fun i hi => ?_⟩
    · have := Nat.mul_le_mul_right d (show i ≤ k - 1 by omega); omega
    · have := hmono i hi
      have e1 : a + 1 + i * d = a + i * d + 1 := by omega
      simpa [e1] using this

lemma set_eq (r k : ℕ) (hk : 1 ≤ k) :
    {M : ℕ | BlindVdw.GoodN r k M} = {N : ℕ | 0 < N ∧ IsRamsey (Fin r) k N} := by
  ext M; exact good_iff r k M hk

/-- `W r k` (an `sInf`) is the least good `N`, for every `k ≥ 1`: no junk value. -/
lemma isVdw_W (r k : ℕ) (hk : 1 ≤ k) : BlindVdw.IsVdwNumber r k (W r k) := by
  unfold BlindVdw.IsVdwNumber W
  rw [set_eq r k hk]
  obtain ⟨N, hN⟩ := vdw_finite r k hk
  exact ⟨Nat.sInf_mem ⟨N, hN⟩, fun m hm => Nat.sInf_le hm⟩

lemma bound_eq (r k : ℕ) :
    BlindVdw.bound r k = (k : ℝ) ^ ((1 / 100000 : ℝ) * k * (Nat.log 2 r : ℝ)) := by
  unfold BlindVdw.bound; norm_num

/-- The frozen statement is equivalent to the blind reading of Theorem 1.1. -/
theorem closure :
    (type_of% @uniform_lower_bound) ↔ (type_of% @BlindVdw.reading) := by
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨max K 1, le_max_right _ _, fun k hk r hr => ⟨W r k, isVdw_W r k (le_of_max_le_right hk),
      ?_⟩⟩
    rw [bound_eq]; exact hK k (le_of_max_le_left hk) r hr
  · rintro ⟨K0, hK0, h⟩
    refine ⟨K0, fun k hk r hr => ?_⟩
    obtain ⟨N, hN, hb⟩ := h k hk r hr
    have : W r k = N := by
      have h1 := isVdw_W r k (le_trans hK0 hk)
      exact h1.unique hN
    rw [this, ← bound_eq]; exact hb

/-- The frozen statement implies the reader's corollary `W_r(k)^{1/k} → ∞` for each `r ≥ 2`. -/
theorem closure_corollary :
    (type_of% @uniform_lower_bound) → (type_of% @BlindVdw.reading_corollary) := by
  rintro ⟨K, hK⟩ r hr
  refine ⟨W r, fun k hk => isVdw_W r k hk, ?_⟩
  set c : ℝ := 1 / 100000 with hc
  have hcpos : 0 < c := by norm_num [hc]
  have hlog : 1 ≤ Nat.log 2 r := Nat.le_log_of_pow_le (by norm_num) (by simpa using hr)
  have hlim : Tendsto (fun k : ℕ => (k : ℝ) ^ c) atTop atTop :=
    (tendsto_rpow_atTop hcpos).comp tendsto_natCast_atTop_atTop
  refine tendsto_atTop_mono' atTop ?_ hlim
  filter_upwards [eventually_ge_atTop (max K 1)] with k hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast le_of_max_le_right hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hb := hK k (le_of_max_le_left hk) r hr
  have hL : (1 : ℝ) ≤ (Nat.log 2 r : ℝ) := by exact_mod_cast hlog
  calc (k : ℝ) ^ c ≤ (k : ℝ) ^ (c * (Nat.log 2 r : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hk1 (by nlinarith)
    _ = ((k : ℝ) ^ (c * k * (Nat.log 2 r : ℝ))) ^ ((1 : ℝ) / k) := by
        rw [← Real.rpow_mul hk0.le]; congr 1; field_simp
    _ ≤ (W r k : ℝ) ^ ((1 : ℝ) / k) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hk0.le _) hb.le (by positivity)

/-- The frozen statement implies the reader's form of Erdős's question (two colours). -/
theorem closure_erdos :
    (type_of% @uniform_lower_bound) → (type_of% @BlindVdw.reading_erdos) :=
  fun h => closure_corollary h 2 le_rfl

end ExternalS.Vdw

#print axioms ExternalS.Vdw.vdw_finite
#print axioms ExternalS.Vdw.closure
#print axioms ExternalS.Vdw.closure_corollary
#print axioms ExternalS.Vdw.closure_erdos
