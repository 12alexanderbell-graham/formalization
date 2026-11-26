import ComparatorChallenges.ErdosReciprocal
import Readings.Erdos3

/-! Post-verdict part-3 test: closure of the blind reading of family 159 (Erdős 3) against the frozen
statement `OAI.Erdos3.manuscriptReciprocalProgressionTheorem`. Result: frozen ⟺ `reading_erdos`;
the manuscript's Theorem 1.1 (`reading`, the quantitative bound r_k(N) ≤ C N exp(−c (log N)^ε))
has no counterpart in the frozen statement — the Lean covers the corollary, not the headline. -/

namespace ExternalS.Erdos3
open OAI.Erdos3

lemma recip_eq (A : Set ℕ) : reciprocalTerm A = A.indicator (fun n : ℕ => (n : ℝ)⁻¹) := by
  funext n; simp only [reciprocalTerm, Set.indicator]

lemma summable_iff (A : Set ℕ) :
    Summable (fun n : A => (1 : ℝ) / (n : ℕ)) ↔ Summable (reciprocalTerm A) := by
  rw [recip_eq, ← summable_subtype_iff_indicator]; simp [Function.comp_def, one_div]

theorem closure : (type_of% @manuscriptReciprocalProgressionTheorem) ↔ (type_of% @reading_erdos) := by
  constructor
  · intro h A _ hns k
    exact h A (fun hs => hns ((summable_iff A).mpr hs)) k
  · intro h A hns k
    set A' : Set ℕ := {n | n ∈ A ∧ 0 < n}
    have heq : reciprocalTerm A' = reciprocalTerm A := by
      rw [recip_eq, recip_eq]; funext n
      by_cases hn : n = 0
      · subst hn; by_cases hA : (0 : ℕ) ∈ A <;> simp [Set.indicator, hA, A']
      · by_cases hA : n ∈ A <;> simp [Set.indicator, hA, A', Nat.pos_of_ne_zero hn]
    obtain ⟨a, d, hd, hap⟩ := h A' (fun n hn => hn.2)
      (fun hs => hns (heq ▸ (summable_iff A').mp hs)) k
    exact ⟨a, d, hd, fun i hi => (hap i hi).1⟩

end ExternalS.Erdos3
#print axioms ExternalS.Erdos3.closure
