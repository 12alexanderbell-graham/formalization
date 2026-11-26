import ComparatorChallenges.ShortEgyptianFractions
import Readings.Egyptian

/-! Closure of the blind reading (runs/2026-11-26T1529Z/S/egyptian/reading.lean) against the
frozen comparator statement `OAI.ShortEgyptian.main` of the OpenAI release (family 025).
Statements are taken with `type_of%`, never retyped. -/

namespace ExternalS.Egyptian

/-- The frozen `IsExpansion` elaborates `ns.map (fun n => (1 : ℚ) / (n : ℚ))` by lifting the list
`ns : List ℕ` into `List ℚ` through the list monad; this rewrites it to the plain map. -/
lemma key (l : List ℕ) : (List.map (fun n : ℚ => 1 / n) (do let a ← l; pure (a:ℚ))) =
    l.map (fun n : ℕ => 1 / (n:ℚ)) := by
  induction l with
  | nil => rfl
  | cons x t ih => simp only [List.map_cons] at *; rw [← ih]; rfl

lemma exp_iff (a b k : ℕ) :
    (∃ ns : List ℕ, OAI.ShortEgyptian.IsExpansion a b ns ∧ ns.length = k) ↔
      EgyptianReading.IsExpansion a b k := by
  constructor
  · rintro ⟨ns, ⟨hp, h2, hs⟩, rfl⟩
    rw [← List.ofFn_get ns] at hp h2 hs
    refine ⟨ns.get, ?_, ?_, ?_⟩
    · intro i j hij; exact List.pairwise_ofFn.mp hp hij
    · intro i; exact h2 _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
    · rw [key, List.map_ofFn, List.sum_ofFn] at hs; simpa using hs
  · rintro ⟨n, hn, h2, hs⟩
    refine ⟨List.ofFn n, ⟨?_, ?_, ?_⟩, List.length_ofFn⟩
    · exact List.pairwise_ofFn.mpr (fun i j hij => hn hij)
    · intro x hx; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx; exact h2 i
    · rw [key, List.map_ofFn, List.sum_ofFn]; simpa using hs

lemma minLength_eq (a b : ℕ) : OAI.ShortEgyptian.minLength a b = EgyptianReading.N2 a b := by
  unfold OAI.ShortEgyptian.minLength EgyptianReading.N2
  congr 1; ext k; exact exp_iff a b k

lemma maxMin_eq (b : ℕ) : OAI.ShortEgyptian.maxMinLength b = EgyptianReading.N b := by
  unfold OAI.ShortEgyptian.maxMinLength EgyptianReading.N
  simp only [minLength_eq]

/-- The frozen statement is equivalent to the blind reading of Theorem 1.1 together with the
existence of expansions (which the reader stated as a separate theorem `exists_expansion`). -/
theorem closure :
    (type_of% @OAI.ShortEgyptian.main) ↔
      ((type_of% @EgyptianReading.reading) ∧ (type_of% @EgyptianReading.exists_expansion)) := by
  constructor
  · rintro ⟨hex, c₁, c₂, h1, h2, b₀, hb₀, hb⟩
    refine ⟨⟨c₁, c₂, h1, h2, b₀, fun b hb' => ?_⟩, fun a b ha hab => ?_⟩
    · simpa [maxMin_eq] using hb b hb'
    · obtain ⟨ns, hns⟩ := hex a b ha hab
      exact ⟨ns.length, (exp_iff a b _).mp ⟨ns, hns, rfl⟩⟩
  · rintro ⟨⟨c₁, c₂, h1, h2, b₀, hb⟩, hex⟩
    refine ⟨fun a b ha hab => ?_, c₁, c₂, h1, h2, max b₀ 2, le_max_right _ _, fun b hb' => ?_⟩
    · obtain ⟨k, hk⟩ := hex a b ha hab
      obtain ⟨ns, hns, -⟩ := (exp_iff a b k).mpr hk
      exact ⟨ns, hns⟩
    · simpa [maxMin_eq] using hb b (le_of_max_le_left hb')

/-- The frozen statement implies the reader's form of Erdős Problem 304. -/
theorem closure_erdos :
    (type_of% @OAI.ShortEgyptian.main) → (type_of% @EgyptianReading.reading_erdos) := by
  intro h
  obtain ⟨⟨c₁, c₂, h1, h2, b₀, hb⟩, -⟩ := closure.mp h
  exact ⟨c₂, h2, b₀, fun b hb' => (hb b hb').2⟩

end ExternalS.Egyptian
#print axioms ExternalS.Egyptian.closure
#print axioms ExternalS.Egyptian.closure_erdos
