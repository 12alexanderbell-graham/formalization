import Mathlib

namespace ReaderB

open Matroid

variable {E Θ : Type*}

/-- Contraction onto X: M.X = M／(E \ X). -/
def contractOnto (M : Matroid E) (X : Set E) : Matroid E := M.contract (M.E \ X)

/-- Spanning: closure is the whole ground set. -/
def Spanning' (M : Matroid E) (S : Set E) : Prop := M.closure S = M.E

/-- Packing/covering partition for a family (M i) on ground set univ. -/
def HasPCPartition (M : Θ → Matroid E) : Prop :=
  ∃ (P C : Set E) (S I : Θ → Set E),
    Disjoint P C ∧ P ∪ C = Set.univ ∧
    (∀ i, S i ⊆ P) ∧ (∀ i, I i ⊆ C) ∧
    (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧
    (∀ i, ((M i).restrict P).closure (S i) = P) ∧
    (∀ i, (contractOnto (M i) C).Indep (I i)) ∧
    (⋃ i, I i) = C

/-- Pair satisfies intersection. -/
def SatisfiesIntersection (M N : Matroid E) : Prop :=
  ∃ J, M.Indep J ∧ N.Indep J ∧ ∃ JM JN, Disjoint JM JN ∧ JM ∪ JN = J ∧
    M.closure JM ∪ N.closure JN = M.E

/-- Theorem 1.1. -/
theorem readingMatroidMain :
    ∃ (E : Type) (_ : Countable E) (_ : Infinite E) (M₀ M₁ : Matroid E),
      M₀.E = Set.univ ∧ M₁.E = Set.univ ∧ M₀✶ = M₀ ∧ M₁✶ = M₁ ∧
      (∀ I₀ I₁, M₀.Indep I₀ → M₁.Indep I₁ → I₀ ∪ I₁ ≠ Set.univ) ∧
      ¬ HasPCPartition (fun b : Bool => if b then M₁ else M₀) := sorry

/-- Corollary 1.4: the same pair does not satisfy intersection (also in the explicit form). -/
theorem readingMatroidCor :
    ∃ (E : Type) (_ : Countable E) (_ : Infinite E) (M₀ M₁ : Matroid E),
      M₀.E = Set.univ ∧ M₁.E = Set.univ ∧ M₀✶ = M₀ ∧ M₁✶ = M₁ ∧
      (∀ I₀ I₁, M₀.Indep I₀ → M₁.Indep I₁ → I₀ ∪ I₁ ≠ Set.univ) ∧
      ¬ HasPCPartition (fun b : Bool => if b then M₁ else M₀) ∧
      ¬ SatisfiesIntersection M₀ M₁ ∧
      ∀ J J₀ J₁, M₀.Indep J → M₁.Indep J → Disjoint J₀ J₁ → J₀ ∪ J₁ = J →
        M₀.closure J₀ ∪ M₁.closure J₁ ≠ Set.univ := sorry

/-
Ambiguities / choices:
- Ground set: type E with matroids having `M.E = univ` (Mathlib matroids have a ground-set field);
  countably infinite = `Countable E ∧ Infinite E`. "Same labelled ground set" = M.E = univ for both.
- Self-dual: `M✶ = M` (Matroid equality, incl. ground set).
- Family indexed by Θ = Bool, M₀ at false, M₁ at true.
- Restriction `M.restrict P` (M ↾ P); closure in it of S ⊆ P; S i ⊆ P and I i ⊆ C required explicitly
  (source says so), so no junk from closure of sets outside ground.
- Contraction onto C: M.contract (M.E \ C); independence in it of I i ⊆ C.
- Partition: Disjoint P C and P ∪ C = univ (empty parts allowed).
- Spanning' defined but only implicitly the closure condition is used.
- Intersection: Mathlib closure of J₀ ⊆ E is genuine as J₀ ⊆ J independent hence ⊆ ground.
- Corollary: stated for the same pair as in Theorem 1.1 (existential repeated with conclusions),
  with both the defined property and the explicit closure form.
-/

end ReaderB
