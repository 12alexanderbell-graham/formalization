import Mathlib

namespace ReaderA

open Matroid
open scoped Matroid

universe u

variable {α : Type u}

/-- Restriction `M ↾ X` (Mathlib's `Matroid.restrict`). -/
def restr (M : Matroid α) (X : Set α) : Matroid α := M.restrict X

/-- Contraction onto `X`: `M.X := M / (E \ X) = (M* ↾ X)*`; we use the right-hand form. -/
def contractOnto (M : Matroid α) (X : Set α) : Matroid α := (M.dual.restrict X).dual

/-- A set is spanning if its closure is the whole ground set. -/
def IsSpanning (M : Matroid α) (S : Set α) : Prop := M.closure S = M.E

/-- A packing/covering partition for a family `(M i : i ∈ Θ)` of matroids on `E`:
`E = P ⊔ C` with `S i ⊆ P`, `I i ⊆ C`, the `S i` pairwise disjoint,
`cl_{M i ↾ P}(S i) = P`, `I i` independent in `(M i).C`, and `⋃ I i = C`. -/
def HasPackingCoveringPartition {Θ : Type*} (E : Set α) (M : Θ → Matroid α) : Prop :=
  ∃ (P C : Set α) (S I : Θ → Set α),
    Disjoint P C ∧ P ∪ C = E ∧
    (∀ i, S i ⊆ P) ∧ (∀ i, I i ⊆ C) ∧
    (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧
    (∀ i, ((M i).restrict P).closure (S i) = P) ∧
    (∀ i, (contractOnto (M i) C).Indep (I i)) ∧
    (⋃ i, I i) = C

/-- `M` is uniform: replacing any element of any basis by any element outside that basis
(in the ground set) again gives a basis. -/
def IsUniform (M : Matroid α) : Prop :=
  ∀ B, M.IsBase B → ∀ x ∈ B, ∀ y ∈ M.E \ B, M.IsBase (insert y (B \ {x}))

/-- `M` is partitional: a direct sum of uniform matroids. Concretely, the ground set is a
disjoint union of parts `F k`, each restriction `M ↾ F k` is uniform, and a subset of `E`
is independent iff its trace on every part is independent in that part. -/
def IsPartitional (M : Matroid α) : Prop :=
  ∃ (κ : Type u) (F : κ → Set α),
    (∀ k l, k ≠ l → Disjoint (F k) (F l)) ∧ (⋃ k, F k) = M.E ∧
    (∀ k, IsUniform (M.restrict (F k))) ∧
    ∀ I ⊆ M.E, M.Indep I ↔ ∀ k, (M.restrict (F k)).Indep (I ∩ F k)

/-- The pair `(M, N)` on common ground set `E` satisfies intersection. -/
def SatisfiesIntersection (E : Set α) (M N : Matroid α) : Prop :=
  ∃ J JM JN : Set α, M.Indep J ∧ N.Indep J ∧ Disjoint JM JN ∧ JM ∪ JN = J ∧
    M.closure JM ∪ N.closure JN = E

/-- The conclusions of Theorem 1.1 for a pair `M0, M1` on `E`. -/
def Thm11Props (E : Set α) (M0 M1 : Matroid α) : Prop :=
  E.Countable ∧ E.Infinite ∧ M0.E = E ∧ M1.E = E ∧
  M0.dual = M0 ∧ M1.dual = M1 ∧
  (∀ I0 I1, M0.Indep I0 → M1.Indep I1 → I0 ∪ I1 ≠ E) ∧
  ¬ HasPackingCoveringPartition E (fun i : Fin 2 => if i = 0 then M0 else M1)

/-- Theorem 1.1. -/
theorem reading_main :
    ∃ (α : Type) (E : Set α) (M0 M1 : Matroid α), Thm11Props E M0 M1 := sorry

/-- Theorem 1.1, last sentence: the infinite matroid packing/covering conjecture
(every set-indexed family of matroids on a common ground set has a packing/covering
partition) is false. -/
theorem reading_conjecture_false :
    ¬ ∀ (α : Type) (E : Set α) (Θ : Type) (M : Θ → Matroid α),
        (∀ i, (M i).E = E) → HasPackingCoveringPartition E M := sorry

/-- Corollary 1.4: a pair as in Theorem 1.1 which moreover consists of partitional
matroids and does not satisfy intersection: for every `J` independent in both and every
partition `J = J0 ⊔ J1`, `cl_{M0}(J0) ∪ cl_{M1}(J1) ≠ E`. -/
theorem reading_intersection :
    ∃ (α : Type) (E : Set α) (M0 M1 : Matroid α), Thm11Props E M0 M1 ∧
      IsPartitional M0 ∧ IsPartitional M1 ∧
      ∀ J J0 J1 : Set α, M0.Indep J → M1.Indep J → Disjoint J0 J1 → J0 ∪ J1 = J →
        M0.closure J0 ∪ M1.closure J1 ≠ E := sorry

/-- Corollary 1.4, consequence: the unrestricted infinite Matroid Intersection Conjecture
is false. -/
theorem reading_MIC_false :
    ¬ ∀ (α : Type) (M N : Matroid α), M.E = N.E → SatisfiesIntersection M.E M N := sorry

/-- Corollary 1.4, consequence: negative answer to Joó's Question 1.5 (intersection for two
partitional matroids on a common countable ground set). -/
theorem reading_joo_question :
    ¬ ∀ (α : Type) (M N : Matroid α), M.E = N.E → M.E.Countable →
        IsPartitional M → IsPartitional N → SatisfiesIntersection M.E M N := sorry

end ReaderA

/-
Ambiguities and choices (reader A):

1. Infinite matroids: Mathlib's `Matroid α` (independence axioms incl. the maximal
   extension axiom; finitary not assumed), ground set `M.E : Set α`. "Countably infinite
   set E": `E : Set α` with `E.Countable ∧ E.Infinite`, and both matroids have ground set E.
   `α : Type` (universe 0); "In ZFC" is the ambient logic, not formalized further.
2. "M_i^* = M_i on the same labelled ground set": `M.dual = M` (equality of matroids;
   the dual has the same ground set).
3. Restriction: Mathlib `Matroid.restrict`. Contraction onto X: defined as
   `(M✶ ↾ X)✶`, the source's second expression; it equals `M ／ (E \ X)` in Mathlib.
4. Spanning (`IsSpanning`, closure = ground set) is defined as in the source; the
   partition condition is written directly as `cl_{M_i ↾ P}(S_i) = P` exactly as displayed.
   Mathlib's `closure` intersects with the ground set first; since `S i ⊆ P` this is moot.
5. Packing/covering partition: P, C disjoint with union E (parts may be empty),
   S_i ⊆ P, I_i ⊆ C, pairwise disjoint S_i, closure condition, independence in M_i.C,
   ⋃ I_i = C. Family indexed by `Fin 2` with `0 ↦ M0`, `1 ↦ M1`.
6. "Independent covering fails": for all I0 indep in M0 and I1 indep in M1, I0 ∪ I1 ≠ E.
7. "Packing/covering conjecture": every set-indexed family of matroids on a common
   ground set has a packing/covering partition; stated with `Θ : Type`, `α : Type`.
8. Uniform: the source's basis-exchange definition, with "outside that basis" read as
   "in E \ B". Partitional (Joó): a direct sum of uniform matroids, encoded as a partition
   of E into parts F k such that M is the direct sum of its restrictions to the parts
   (independence is checked partwise) and each restriction is uniform. Index type κ is in
   the same universe as α (`Type _`). Not using Mathlib's `Matroid.sigma` to keep the
   definition self-contained.
9. Satisfies intersection: J independent in both, J = J_M ⊔ J_N (disjoint union),
   cl_M(J_M) ∪ cl_N(J_N) = E, where E is the common ground set.
10. Corollary 1.4 "the same pair": stated as existence of a pair satisfying all the
   conclusions of Theorem 1.1 (`Thm11Props`) together with partitionality and failure of
   intersection; the explicit failure form is stated (it is equivalent to
   `¬ SatisfiesIntersection E M0 M1`). The two "Consequently" sentences are separate
   theorems.
-/
