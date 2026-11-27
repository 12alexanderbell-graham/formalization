import Mathlib
import Readings.hochschild
import ComparatorChallenges.KadisonRingrose

/-! # Target O, family O54 (Kadison–Ringrose cohomology conjecture): closures (run 2026-11-27T1628Z).

Frozen statement `OAI.BoundedHochschild.KadisonRingrose.main_result` (taken by name, never retyped). It asks for
`[CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]`; the readers A and B wrote
`[CStarAlgebra M] [WStarAlgebra M]` only. The extra order is always available: Mathlib's spectral order
`CStarAlgebra.spectralOrder M` is a `StarOrderedRing` (`CStarAlgebra.spectralOrderedRing M`), and the frozen
conclusion does not mention the order, so the closure supplies it (`frozen_any_order`). This also shows the frozen
order hypotheses are never vacuous: every C⋆-algebra has such an order.

Differentials: each reader's differential is proved equal, as a function, to the frozen `differentialValue`
(the merge test `i < j` on `Fin` vs on `ℕ`, `i = j` on `Fin` vs on `ℕ`; reader B's signs are `ℤ`-powers acting by
`ℤ`-smul, equal to the frozen `ℂ`-powers acting by `ℂ`-smul). Degrees: reader A writes `k = n + 1` with `1 ≤ n`,
reader B `k = n + 2`; the frozen `n + 2`.

Reader C (a concrete `StarSubalgebra ℂ (H →L[ℂ] H)` equal to its bicommutant) is not closed: the frozen statement
needs `WStarAlgebra ↥M`, and Mathlib has no instance for a von Neumann algebra on a Hilbert space (the predual is
not constructed; `Mathlib/Analysis/VonNeumannAlgebra/Basic.lean` says it "will later" be). Blocker. -/

namespace TargetO.KR

open OAI.BoundedHochschild

universe u

/-- The frozen statement, with the order supplied by the spectral order. -/
theorem frozen_any_order
    (frozen : ∀ {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]
      (n : ℕ) (f : Cochain M (n + 2)), (∀ x : Fin (n + 3) → M, differentialValue f x = 0) →
      ∃ g : Cochain M (n + 1), ∀ x : Fin (n + 2) → M, differentialValue g x = f x)
    {M : Type u} [CStarAlgebra M] [WStarAlgebra M] (n : ℕ) (f : Cochain M (n + 2))
    (hf : ∀ x : Fin (n + 3) → M, differentialValue f x = 0) :
    ∃ g : Cochain M (n + 1), ∀ x : Fin (n + 2) → M, differentialValue g x = f x := by
  let _ := CStarAlgebra.spectralOrder M
  have := CStarAlgebra.spectralOrderedRing M
  exact frozen n f hf

/-! ## Reader A -/

theorem mergeAt_eq {M : Type*} [CStarAlgebra M] {k : ℕ} (a : Fin (k + 1) → M) (j : Fin k) :
    ReaderA.mergeAt a j = mergeInputs a j := by
  funext i
  simp only [ReaderA.mergeAt, mergeInputs, Fin.lt_def, Fin.ext_iff]

theorem dA_eq {M : Type*} [CStarAlgebra M] {k : ℕ} (f : Cochain M k) :
    ReaderA.hochschildD (⇑f) = differentialValue f := by
  funext a
  simp only [ReaderA.hochschildD, differentialValue, mergeAt_eq]

theorem closure_A
    (frozen : ∀ {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]
      (n : ℕ) (f : Cochain M (n + 2)), (∀ x : Fin (n + 3) → M, differentialValue f x = 0) →
      ∃ g : Cochain M (n + 1), ∀ x : Fin (n + 2) → M, differentialValue g x = f x)
    (M : Type u) [CStarAlgebra M] [WStarAlgebra M]
    (n : ℕ) (hn : 1 ≤ n) (f : ReaderA.Cb M (n + 1)) (hf : ReaderA.hochschildD (⇑f) = 0) :
    ∃ g : ReaderA.Cb M n, (⇑f : (Fin (n + 1) → M) → M) = ReaderA.hochschildD (⇑g) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hf' : ∀ x : Fin (m + 3) → M, differentialValue f x = 0 := by
    intro x; rw [← dA_eq, hf]; rfl
  obtain ⟨g, hg⟩ := frozen_any_order frozen m f hf'
  exact ⟨g, by rw [dA_eq]; funext x; exact (hg x).symm⟩

theorem reading_A_closed : type_of% @ReaderA.reading_hochschild_main.{u} :=
  closure_A (@KadisonRingrose.main_result.{u})

/-! ## Reader B -/

theorem dB_eq {M : Type*} [CStarAlgebra M] [WStarAlgebra M] {k : ℕ} (f : Cochain M k) :
    ReaderB.dRaw (⇑f) = differentialValue f := by
  funext a
  simp only [ReaderB.dRaw, differentialValue]
  have hs : ∀ (p : ℕ) (x : M), ((-1 : ℤ) ^ p) • x = ((-1 : ℂ) ^ p) • x := by
    intro p x
    rw [← Int.cast_smul_eq_zsmul ℂ]
    push_cast; rfl
  simp only [hs]
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  funext i
  unfold mergeInputs
  by_cases h1 : i < j
  · simp [h1, Fin.lt_def.mp h1]
  · have h1' : ¬ (i : ℕ) < j := fun h => h1 (Fin.lt_def.mpr h)
    by_cases h2 : i = j
    · subst h2; simp
    · have h2' : ¬ (i : ℕ) = j := fun h => h2 (Fin.ext h)
      simp [h1, h1', h2]

theorem closure_B
    (frozen : ∀ {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]
      (n : ℕ) (f : Cochain M (n + 2)), (∀ x : Fin (n + 3) → M, differentialValue f x = 0) →
      ∃ g : Cochain M (n + 1), ∀ x : Fin (n + 2) → M, differentialValue g x = f x)
    {M : Type u} [CStarAlgebra M] [WStarAlgebra M]
    (n : ℕ) (f : ReaderB.Cb M (n + 2)) (hf : ReaderB.dRaw (⇑f) = 0) :
    ∃ g : ReaderB.Cb M (n + 1), ReaderB.dRaw (⇑g) = ⇑f := by
  have hf' : ∀ x : Fin (n + 3) → M, differentialValue f x = 0 := by
    intro x; rw [← dB_eq, hf]; rfl
  obtain ⟨g, hg⟩ := frozen_any_order frozen n f hf'
  exact ⟨g, by rw [dB_eq]; funext x; exact hg x⟩

theorem reading_B_closed : type_of% @ReaderB.readingHochschild.{u} :=
  closure_B (@KadisonRingrose.main_result.{u})

end TargetO.KR

#print axioms TargetO.KR.closure_A
#print axioms TargetO.KR.closure_B
#print axioms TargetO.KR.reading_A_closed
#print axioms TargetO.KR.reading_B_closed
