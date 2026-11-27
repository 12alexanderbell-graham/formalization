import Mathlib

/-! Blind readings A, B, C (code unchanged; only `import Mathlib` hoisted). -/

-- ===== reader A =====

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

-- ===== reader B =====

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

-- ===== reader C =====

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
