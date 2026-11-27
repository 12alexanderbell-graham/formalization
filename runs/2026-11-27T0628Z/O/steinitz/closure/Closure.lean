import Mathlib
import Readings.Steinitz
import ComparatorChallenges.SteinitzBergstrom

/-! # Target O, family O26 (the Euclidean Steinitz–Bergström theorem): closures (run 2026-11-27T0628Z).
Frozen statement taken with `type_of%`, never retyped: one C with both the signed-prefix bound (Theorem 1.1) and
the zero-sum ordering bound (Theorem 1.2), prefix k = the indices below k, unit-ball vectors of
`EuclideanSpace ℝ (Fin d)`. Closed (frozen ⇒ reading): every reader's Theorems 1.1 and 1.2 and readers A and B's
"one constant for both". Not closed: readers A and C's reading of "the constant in Theorem 1.1 also suffices
here" as *every* constant valid for 1.1 is valid for 1.2 — the frozen statement gives only one common C. -/

namespace TargetO.Steinitz

theorem signs_symm {N : ℕ} {ε : Fin N → ℝ} (h : ∀ i, ε i = -1 ∨ ε i = 1) : ∀ i, ε i = 1 ∨ ε i = -1 :=
  fun i => (h i).symm

theorem A_one : (type_of% @OAI.EuclideanSteinitzBergstrom.main) → (type_of% @ReaderA.reading_thm_1_1_and_1_2_one_constant) := by
  rintro ⟨C, hs, ho⟩
  exact ⟨C, fun d N hd hN v hv => hs d N hd hN v hv, fun d N hd hN v hv h0 => ho d N hd hN v hv h0⟩

theorem A_sign : (type_of% @OAI.EuclideanSteinitzBergstrom.main) → (type_of% @ReaderA.reading_thm_1_1_signing) := by
  intro h; obtain ⟨C, hs, -⟩ := A_one h; exact ⟨C, hs⟩

theorem A_steinitz : (type_of% @OAI.EuclideanSteinitzBergstrom.main) → (type_of% @ReaderA.reading_thm_1_2_steinitz) := by
  intro h; obtain ⟨C, -, ho⟩ := A_one h; exact ⟨C, ho⟩

theorem B_same : (type_of% @OAI.EuclideanSteinitzBergstrom.main) → (type_of% @ReaderB.readingSameConstant) := by
  rintro ⟨C, hs, ho⟩
  refine ⟨C, fun d N hd hN v hv => ?_, fun d N hd hN v hv h0 => ho d N hd hN v hv h0⟩
  obtain ⟨ε, he, hb⟩ := hs d N hd hN v hv
  exact ⟨ε, signs_symm he, hb⟩

theorem B_sign : (type_of% @OAI.EuclideanSteinitzBergstrom.main) → (type_of% @ReaderB.readingSigning) := by
  intro h; obtain ⟨C, hs, -⟩ := B_same h; exact ⟨C, hs⟩

theorem B_steinitz : (type_of% @OAI.EuclideanSteinitzBergstrom.main) → (type_of% @ReaderB.readingSteinitz) := by
  intro h; obtain ⟨C, -, ho⟩ := B_same h; exact ⟨C, ho⟩

theorem C_sign : (type_of% @OAI.EuclideanSteinitzBergstrom.main) → (type_of% @ReaderC.reading_thm_1_1_signing) := by
  rintro ⟨C, hs, -⟩
  refine ⟨C, fun d N hd hN v hv => ?_⟩
  obtain ⟨ε, he, hb⟩ := hs d N hd hN v hv
  exact ⟨ε, signs_symm he, hb⟩

theorem C_steinitz : (type_of% @OAI.EuclideanSteinitzBergstrom.main) → (type_of% @ReaderC.reading_thm_1_2_steinitz) := by
  rintro ⟨C, -, ho⟩
  exact ⟨C, fun d N hd hN v hv h0 => ho d N hd hN v hv h0⟩

end TargetO.Steinitz

#print axioms TargetO.Steinitz.A_one
#print axioms TargetO.Steinitz.A_sign
#print axioms TargetO.Steinitz.A_steinitz
#print axioms TargetO.Steinitz.B_same
#print axioms TargetO.Steinitz.B_sign
#print axioms TargetO.Steinitz.B_steinitz
#print axioms TargetO.Steinitz.C_sign
#print axioms TargetO.Steinitz.C_steinitz
