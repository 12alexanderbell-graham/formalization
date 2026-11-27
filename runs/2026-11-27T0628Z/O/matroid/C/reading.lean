import Mathlib

namespace ReaderC

/-- Contraction onto X, from the source: M.X := M/(E \ X) = (M^* restricted to X)^*. -/
def readingContractOnto {α : Type} (M : Matroid α) (X : Set α) : Matroid α :=
  (M.dual.restrict X).dual

/-- A packing/covering partition for the family M : Fin 2 → Matroid α on the ground set `Set.univ`.
It consists of a partition E = P ⊔ C and sets S i ⊆ P, I i ⊆ C with:
pairwise disjoint S i; cl_{M_i ↾ P}(S_i) = P; I_i independent in M_i.C (contraction onto C);
and ⋃ I_i = C. -/
def readingIsPCPartition {α : Type} (M : Fin 2 → Matroid α) (P C : Set α)
    (S I : Fin 2 → Set α) : Prop :=
  P ∪ C = Set.univ ∧ Disjoint P C ∧
  (∀ i, S i ⊆ P) ∧
  (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧
  (∀ i, ((M i).restrict P).closure (S i) = P) ∧
  (∀ i, I i ⊆ C) ∧
  (∀ i, (readingContractOnto (M i) C).Indep (I i)) ∧
  (⋃ i, I i) = C

/-- "Satisfies intersection" for matroids M, N on a common ground set E: there is a set J independent in
both, and a partition J = J_M ⊔ J_N with cl_M(J_M) ∪ cl_N(J_N) = E. -/
def readingSatisfiesIntersection {α : Type} (M N : Matroid α) : Prop :=
  ∃ J J₁ J₂ : Set α, M.Indep J ∧ N.Indep J ∧ Disjoint J₁ J₂ ∧ J₁ ∪ J₂ = J ∧
    M.closure J₁ ∪ N.closure J₂ = M.E

/-- The pair conditions of Theorem 1.1: a countably infinite ground type, two matroids on it with
ground set everything, both self-dual (M_i^* = M_i). -/
def readingPairConditions (α : Type) (M : Fin 2 → Matroid α) : Prop :=
  Countable α ∧ Infinite α ∧ (∀ i, (M i).E = Set.univ) ∧ (∀ i, (M i).dual = M i)

/-- Theorem 1.1, first claim: no independent covering of E. -/
theorem reading_no_independent_covering :
    ∃ (α : Type) (M : Fin 2 → Matroid α), readingPairConditions α M ∧
      ∀ I₀ I₁ : Set α, (M 0).Indep I₀ → (M 1).Indep I₁ → I₀ ∪ I₁ ≠ Set.univ := by
  sorry

/-- Theorem 1.1, second claim: the pair has no packing/covering partition. -/
theorem reading_no_packing_covering_partition :
    ∃ (α : Type) (M : Fin 2 → Matroid α), readingPairConditions α M ∧
      ¬ ∃ P C : Set α, ∃ S I : Fin 2 → Set α, readingIsPCPartition M P C S I := by
  sorry

/-- Theorem 1.1 combined: the pair witnesses both claims at once, in one countable example. -/
theorem reading_main :
    ∃ (α : Type) (M : Fin 2 → Matroid α), readingPairConditions α M ∧
      (∀ I₀ I₁ : Set α, (M 0).Indep I₀ → (M 1).Indep I₁ → I₀ ∪ I₁ ≠ Set.univ) ∧
      ¬ ∃ P C : Set α, ∃ S I : Fin 2 → Set α, readingIsPCPartition M P C S I := by
  sorry

/-- Corollary 1.4: the same pair does not satisfy intersection. -/
theorem reading_cor_1_4 :
    ∃ (α : Type) (M : Fin 2 → Matroid α), readingPairConditions α M ∧
      ¬ readingSatisfiesIntersection (M 0) (M 1) := by
  sorry

/-- Corollary 1.4, explicit form: for every J independent in both matroids and every partition
J = J₀ ⊔ J₁, cl_{M₀}(J₀) ∪ cl_{M₁}(J₁) ≠ E. -/
theorem reading_cor_1_4_explicit :
    ∃ (α : Type) (M : Fin 2 → Matroid α), readingPairConditions α M ∧
      ∀ J J₀ J₁ : Set α, (M 0).Indep J → (M 1).Indep J → Disjoint J₀ J₁ → J₀ ∪ J₁ = J →
        (M 0).closure J₀ ∪ (M 1).closure J₁ ≠ Set.univ := by
  sorry

end ReaderC

/-
Ambiguities and choices (comment block):
* Infinite matroids: Mathlib's `Matroid` follows the Bruhn–Diestel–Kriesell–Pendavingh–Wollan axioms
  (the maximal extension axiom is built in), as the source assumes.
* The ground set E is taken as the whole type `α`, with `(M i).E = Set.univ`. "Countably infinite E" is
  `Countable α ∧ Infinite α`. "Matroids on E" is therefore `(M i).E = Set.univ`.
* Self-dual: `M_i^* = M_i` is `(M i).dual = M i`. This is equality of Mathlib matroid structures, which
  includes the ground set, matching "on the same labelled ground set".
* Restriction is Mathlib's `Matroid.restrict`. Contraction onto X is the source's formula
  `(M^* ↾ X)^*`, written as `readingContractOnto`. I did not use `Matroid.contract` directly.
* Closure: `cl_{M_i ↾ P}(S_i) = P` is `((M i).restrict P).closure (S i) = P`.
* Packing/covering partition: the definition is literal. E = P ⊔ C is `P ∪ C = univ` with `Disjoint P C`.
  The sets S_i ⊆ P and I_i ⊆ C, pairwise disjoint S_i, S_i spanning P in M_i ↾ P, I_i independent in M_i.C,
  and ⋃ I_i = C. Indices are `Fin 2`, the two matroids.
* "Not satisfy intersection": I used the source's definition, with J independent in both, J = J₁ ⊔ J₂
  and cl(J₁) ∪ cl(J₂) = E, where E = M.E = univ. Corollary 1.4 is stated as an existence over
  a pair meeting `readingPairConditions`, reading "the same pair constructed in Theorem 1.1" as "the pair
  from Theorem 1.1". The stronger universal reading is not asserted.
* "Partitional" (Joo's notion) and its consequence in the corollary are not formalised, since Mathlib has no
  definition for it. The corollary's negative answer to Joo's Question 1.5 is also not formalised.
* Packing/covering-conjecture consequence and "in ZFC": not formalised. ZFC is not a Lean statement here.
* The main theorem is `reading_main` (both claims in one existence). The two claims also appear separately.
-/
