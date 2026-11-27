import Mathlib
import Readings.Mahler
import ComparatorChallenges.SymmetricMahlerEquality

/-! # Target O, family O20: reader A's equality case against the family's second challenge
`symmetric_mahler_equality` (run 2026-11-27T0628Z; the challenge was first missed, see EXTERNAL_O.md, Correction).
Frozen statement taken with `type_of%`: for a symmetric convex body K ⊆ (Fin n → ℝ),
(vol K).toReal (vol K°).toReal = 4ⁿ/n! ↔ K is a linear image of a Hanner polytope (`IsHanner`: centred
intervals, `Fin.append` products and convex hulls of the two embedded copies). Reader A's Hanner polytopes are the
frozen ones (proved by induction both ways), its polar is the frozen polar, and its `ℝ≥0∞` equation is the frozen
real one because 0 < vol K < ∞ (an infinite polar volume makes both sides false). Readers B and C (Euclidean
space; C's coordinate blocks) are not closed here. -/

open MeasureTheory

namespace TargetO.MahlerEq

open OAI.SymmetricMahler

theorem interval_eq (a : ℝ) :
    {x : Fin 1 → ℝ | -a ≤ x 0 ∧ x 0 ≤ a} = Set.Icc (fun _ : Fin 1 => -a) (fun _ : Fin 1 => a) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Icc, Pi.le_def]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> rw [Subsingleton.elim i 0] <;> assumption
  · rintro ⟨h1, h2⟩; exact ⟨h1 0, h2 0⟩

theorem hanner_to {n : ℕ} {H : Set (Fin n → ℝ)} (h : ReaderA.IsHanner n H) : IsHanner H := by
  induction h with
  | interval a ha => rw [interval_eq]; exact IsHanner.interval a ha
  | linfSum _ _ ih1 ih2 => exact IsHanner.product ih1 ih2
  | l1Sum _ _ ih1 ih2 => exact IsHanner.join ih1 ih2

theorem hanner_of {n : ℕ} {H : Set (Fin n → ℝ)} (h : IsHanner H) : ReaderA.IsHanner n H := by
  induction h with
  | interval a ha => rw [← interval_eq]; exact ReaderA.IsHanner.interval a ha
  | product _ _ ih1 ih2 => exact ReaderA.IsHanner.linfSum ih1 ih2
  | join _ _ ih1 ih2 => exact ReaderA.IsHanner.l1Sum ih1 ih2

theorem linear_iff {n : ℕ} (K : Set (Fin n → ℝ)) : ReaderA.IsLinearHannerBody K ↔ IsLinearHanner K := by
  constructor
  · rintro ⟨T, H, hH, rfl⟩; exact ⟨H, hanner_to hH, T, rfl⟩
  · rintro ⟨H, hH, T, rfl⟩; exact ⟨T, H, hanner_of hH, rfl⟩

/-- `a * b = ofReal c` in `ℝ≥0∞` iff `a.toReal * b.toReal = c`, for 0 < a < ∞ and c > 0. -/
theorem eq_iff {a b : ENNReal} {c : ℝ} (ha0 : a ≠ 0) (hat : a ≠ ⊤) (hc : 0 < c) :
    a * b = ENNReal.ofReal c ↔ a.toReal * b.toReal = c := by
  by_cases hb : b = ⊤
  · subst hb
    rw [ENNReal.mul_top ha0, ENNReal.toReal_top, mul_zero]
    exact ⟨fun h => absurd h.symm ENNReal.ofReal_ne_top, fun h => absurd h hc.ne⟩
  · rw [← ENNReal.toReal_mul]
    constructor
    · intro h; rw [h, ENNReal.toReal_ofReal hc.le]
    · intro h
      rw [← h, ENNReal.ofReal_toReal (ENNReal.mul_ne_top hat hb)]

theorem A_eq : (type_of% @OAI.SymmetricMahler.symmetric_mahler_equality) →
    (type_of% @ReaderA.reading_mahler_equality) := by
  intro h n hn K hK hsymm
  obtain ⟨hc, hconv, hint⟩ := hK
  have hs : ∀ x ∈ K, -x ∈ K := fun x hx => by
    rw [← hsymm]; exact Set.neg_mem_neg.mpr hx
  have hpol : ReaderA.polarBody K = coordinatePolar K := by
    ext y
    simp only [ReaderA.polarBody, ReaderA.dotR, coordinatePolar, Set.mem_setOf_eq]
    refine forall₂_congr fun x _ => ?_
    rw [Finset.sum_congr rfl fun i _ => mul_comm (x i) (y i)]
  have h0 : volume K ≠ 0 := by
    obtain ⟨x, hx⟩ := hint
    exact (MeasureTheory.Measure.measure_pos_of_nonempty_interior volume ⟨x, hx⟩).ne'
  have ht : volume K ≠ ⊤ := hc.measure_lt_top.ne
  have hcpos : (0 : ℝ) < (4 : ℝ) ^ n / (n.factorial : ℝ) := by
    have := Nat.factorial_pos n; positivity
  have hconst : (4 : ENNReal) ^ n / (n.factorial : ENNReal) =
      ENNReal.ofReal ((4 : ℝ) ^ n / (n.factorial : ℝ)) := by
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast Nat.factorial_pos n),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_natCast]
    norm_num
  rw [hpol, hconst, eq_iff h0 ht hcpos, linear_iff]
  exact h hn hc hconv hs hint

end TargetO.MahlerEq

#print axioms TargetO.MahlerEq.A_eq
