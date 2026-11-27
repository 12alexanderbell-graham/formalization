import Mathlib
import Readings.Catalan
import ComparatorChallenges.Catalan

/-! # Target O, family O2 (Catalan's constant is irrational): closures (run 2026-11-27T0628Z).
Frozen statement taken with `type_of%`, never retyped. -/

namespace TargetO.Catalan

/-- `L(2, χ₋₄)` is the frozen series (classical; proved here, odd/even split of the L-series). -/
theorem catalan_LSeries :
    LSeries (fun n : ℕ => ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℂ)) 2 =
      ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) := by
  set f : ℕ → ℂ := fun n => ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℂ)
  have hsum : LSeriesSummable f 2 :=
    ZMod.LSeriesSummable_of_one_lt_re (fun x : ZMod 4 => ((ZMod.χ₄ x : ℤ) : ℂ)) (by norm_num)
  have hev : ∀ k, LSeries.term f 2 (2 * k) = 0 := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero (by omega)]
      have : ZMod.χ₄ ((2 * k : ℕ) : ZMod 4) = 0 := by
        rw [ZMod.χ₄_nat_eq_if_mod_four]; simp [Nat.mul_mod_right]
      show ((ZMod.χ₄ ((2 * k : ℕ) : ZMod 4) : ℤ) : ℂ) / _ = 0
      rw [this]; simp
  have hodd : ∀ k, LSeries.term f 2 (2 * k + 1) = ((-1 : ℝ) ^ k / ((2 * k + 1 : ℕ) : ℝ) ^ 2 : ℝ) := by
    intro k
    rw [LSeries.term_of_ne_zero (by omega)]
    have hχ : ZMod.χ₄ ((2 * k + 1 : ℕ) : ZMod 4) = (-1) ^ k := by
      rw [ZMod.χ₄_nat_eq_if_mod_four]
      have h2 : (2 * k + 1) % 2 ≠ 0 := by omega
      rw [ite_eq_right h2]
      rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · rw [ite_eq_left (by omega)]; simp [pow_add, ← two_mul, pow_mul]
      · rw [ite_eq_right (by omega)]; simp [pow_add, pow_mul]
    simp only [f, hχ]
    push_cast
    rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
  have hs := hsum
  unfold LSeriesSummable at hs
  rw [LSeries, ← tsum_even_add_odd (hs.comp_injective (fun a b h => by omega))
    (hs.comp_injective (fun a b h => by omega))]
  simp only [hev, tsum_zero, zero_add, hodd]
  rw [Complex.ofReal_tsum]

theorem sum_eq : (∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) =
    ∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℝ) ^ 2) := by
  push_cast; rfl

theorem A_reading : (type_of% @OAI.InternalCatalan.catalan_irrational) ↔
    (type_of% @ReaderA.BlindReadingA.Catalan.reading) := by
  show _ ↔ Irrational ReaderA.BlindReadingA.Catalan.CatalanConstant
  unfold ReaderA.BlindReadingA.Catalan.CatalanConstant; rw [sum_eq]

theorem A_reading_alt : (type_of% @OAI.InternalCatalan.catalan_irrational) →
    (type_of% @ReaderA.BlindReadingA.Catalan.reading_alt) := by
  intro _
  show ((ReaderA.BlindReadingA.Catalan.CatalanConstant : ℝ) : ℂ) =
      LSeries (fun n : ℕ => ReaderA.BlindReadingA.Catalan.chiMinus4 n) 2
  unfold ReaderA.BlindReadingA.Catalan.CatalanConstant ReaderA.BlindReadingA.Catalan.chiMinus4
  rw [catalan_LSeries, sum_eq]

theorem B_reading : (type_of% @OAI.InternalCatalan.catalan_irrational) ↔
    (type_of% @ReaderB.reading) := by
  show _ ↔ Irrational ReaderB.CatalanConstant
  unfold ReaderB.CatalanConstant; rw [sum_eq]

theorem B_reading_alt : (type_of% @OAI.InternalCatalan.catalan_irrational) ↔
    (type_of% @ReaderB.reading_alt) := by
  show _ ↔ Irrational (ReaderB.dirichletBeta 2)
  unfold ReaderB.dirichletBeta
  simp only [Real.rpow_two]
  rw [sum_eq]

theorem B_reading_L : (type_of% @OAI.InternalCatalan.catalan_irrational) →
    (type_of% @ReaderB.reading_L) := by
  intro h q hq
  rw [catalan_LSeries] at hq
  exact h ⟨q, by exact_mod_cast hq.symm⟩

theorem C_reading : (type_of% @OAI.InternalCatalan.catalan_irrational) ↔
    (type_of% @ReaderC.reading) := by
  show _ ↔ Irrational ReaderC.CatalanConstant
  unfold ReaderC.CatalanConstant; rw [sum_eq]

theorem C_reading_alt_L : (type_of% @OAI.InternalCatalan.catalan_irrational) →
    (type_of% @ReaderC.reading_alt_L) := by
  intro h
  exact ⟨_, catalan_LSeries, h⟩

end TargetO.Catalan

#print axioms TargetO.Catalan.catalan_LSeries
#print axioms TargetO.Catalan.A_reading
#print axioms TargetO.Catalan.A_reading_alt
#print axioms TargetO.Catalan.B_reading
#print axioms TargetO.Catalan.B_reading_alt
#print axioms TargetO.Catalan.B_reading_L
#print axioms TargetO.Catalan.C_reading
#print axioms TargetO.Catalan.C_reading_alt_L
