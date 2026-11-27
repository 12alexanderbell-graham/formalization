import Mathlib
import Readings.Hadamard
import ComparatorChallenges.CirculantHadamard

/-! # Target O, family O22 (the circulant Hadamard conjecture): closures (run 2026-11-27T0628Z).
Frozen statements taken with `type_of%`, never retyped: `exists_iff_order_one_or_four` (for n > 0, a real
sign matrix H with H Hᵀ = n I and H i j = h (j − i) in `Fin n` exists iff n ∈ {1, 4}) and
`even_length_eq_two_or_four` (a Barker sequence of positive even length has length 2 or 4). Closed: every
reader's Theorem 1.1, by proving each reader's existence statement equivalent to the frozen one (A indexes by
`Fin n` subtraction and asks the signs of h, which the first row gives; B and C index by `ZMod n`, carried to
`Fin n` by `ZMod.finEquiv`). Not closed: every reader's Corollary 1.2 (Barker lengths): the release states
only its even case; the odd case (Turyn–Storer, cited) and the existence of the seven lengths are not in it. -/

namespace TargetO.Hadamard

open OAI.CirculantHadamard

theorem e_apply (k : ℕ) (j : Fin (k + 1)) : ((j : ℕ) : ZMod (k + 1)) = ZMod.finEquiv (k + 1) j := by
  apply ZMod.val_injective
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt j.2]
  rfl

theorem e_sub (k : ℕ) (i j : Fin (k + 1)) :
    ((j : ℕ) : ZMod (k + 1)) - ((i : ℕ) : ZMod (k + 1)) = ZMod.finEquiv (k + 1) (j - i) := by
  rw [e_apply, e_apply, map_sub]

/-- First-row signs: in a frozen circulant sign matrix, `h m = H 0 m` is a sign. -/
theorem h_sign {k : ℕ} {H : RealMatrix (k + 1)} {h : Fin (k + 1) → ℝ} (hc : ∀ i j, H i j = h (j - i))
    (hs : ∀ i j, IsSign (H i j)) (m : Fin (k + 1)) : h m = 1 ∨ h m = -1 := by
  have := hs 0 m
  rw [hc, sub_zero] at this
  exact this

/-- Reader B's circulant Hadamard existence is the frozen one. -/
theorem B_iff (k : ℕ) : ExistsRealCirculantHadamard (k + 1) ↔ ReaderB.IsCirculantHadamard (k + 1) := by
  constructor
  · rintro ⟨H, ⟨h, hc⟩, hs, hHH⟩
    refine ⟨fun z => h ((ZMod.finEquiv (k + 1)).symm z), fun z => h_sign hc hs _, ?_⟩
    have hM : (Matrix.of fun i j : Fin (k + 1) =>
        (fun z => h ((ZMod.finEquiv (k + 1)).symm z)) (((j : ℕ) : ZMod (k + 1)) - ((i : ℕ) : ZMod (k + 1)))) = H := by
      ext i j
      simp only [Matrix.of_apply, e_sub, RingEquiv.symm_apply_apply, hc]
    show (Matrix.of fun i j : Fin (k + 1) =>
        (fun z => h ((ZMod.finEquiv (k + 1)).symm z)) (((j : ℕ) : ZMod (k + 1)) - ((i : ℕ) : ZMod (k + 1)))) *
        (Matrix.of fun i j : Fin (k + 1) =>
        (fun z => h ((ZMod.finEquiv (k + 1)).symm z)) (((j : ℕ) : ZMod (k + 1)) - ((i : ℕ) : ZMod (k + 1)))).transpose = _
    rw [hM]; exact hHH
  · rintro ⟨h', hs, hHH⟩
    refine ⟨Matrix.of fun i j : Fin (k + 1) => h' (((j : ℕ) : ZMod (k + 1)) - ((i : ℕ) : ZMod (k + 1))),
      ⟨fun m => h' (ZMod.finEquiv (k + 1) m), fun i j => ?_⟩, ⟨fun i j => hs _, hHH⟩⟩
    simp only [Matrix.of_apply, e_sub]

/-- Reader C's. -/
theorem C_iff (k : ℕ) : ExistsRealCirculantHadamard (k + 1) ↔
    ∃ H : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ, ReaderC.IsCirculantHadamard (k + 1) H := by
  have hz : ∀ i j : Fin (k + 1), ((((j : ℤ) - (i : ℤ) : ℤ)) : ZMod (k + 1)) = ZMod.finEquiv (k + 1) (j - i) := by
    intro i j
    rw [← e_sub]; push_cast; rfl
  constructor
  · rintro ⟨H, ⟨h, hc⟩, hs, hHH⟩
    refine ⟨H, hs, fun z => h ((ZMod.finEquiv (k + 1)).symm z), fun z => h_sign hc hs _, fun i j => ?_, hHH⟩
    simp only [hz, RingEquiv.symm_apply_apply, hc]
  · rintro ⟨H, hs, h', -, hc, hHH⟩
    refine ⟨H, ⟨fun m => h' (ZMod.finEquiv (k + 1) m), fun i j => ?_⟩, hs, hHH⟩
    rw [hc, hz]

/-- Reader A's. -/
theorem A_iff (k : ℕ) : ExistsRealCirculantHadamard (k + 1) ↔
    ∃ H : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ, ReaderA.IsRealHadamard H ∧ ReaderA.IsCirculant H := by
  constructor
  · rintro ⟨H, ⟨h, hc⟩, hs, hHH⟩
    exact ⟨H, ⟨fun i j => (hs i j).symm, hHH⟩, h, fun m => (h_sign hc hs m).symm, hc⟩
  · rintro ⟨H, ⟨hs, hHH⟩, h, -, hc⟩
    exact ⟨H, ⟨h, hc⟩, fun i j => (hs i j).symm, hHH⟩

theorem A_thm : (type_of% @OAI.CirculantHadamard.exists_iff_order_one_or_four) →
    (type_of% @ReaderA.reading_thm_1_1) := by
  intro h n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [← A_iff]; exact h _ hn

theorem B_thm : (type_of% @OAI.CirculantHadamard.exists_iff_order_one_or_four) →
    (type_of% @ReaderB.readingCirculantHadamard) := by
  intro h n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [← B_iff, h _ hn]
  simp

theorem C_thm : (type_of% @OAI.CirculantHadamard.exists_iff_order_one_or_four) →
    (type_of% @ReaderC.readingC_circulant_hadamard) := by
  intro h n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [← C_iff]; exact h _ hn

end TargetO.Hadamard

#print axioms TargetO.Hadamard.A_thm
#print axioms TargetO.Hadamard.B_thm
#print axioms TargetO.Hadamard.C_thm
