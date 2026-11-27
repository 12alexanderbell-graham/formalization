import Mathlib

/-!
Blind reading A of O32, Theorem 1.1 (Boone–Higman):
for every finitely generated group `G`, `G` has decidable word problem iff `G` embeds in a
finitely presented simple group.
-/

namespace ReaderA

/-- A word in the generators `Fin n` and their inverses: a letter `(i, true)` stands for the
generator `gᵢ`, a letter `(i, false)` for `gᵢ⁻¹`. -/
abbrev Word (n : ℕ) := List (Fin n × Bool)

/-- The element of `G` represented by a word, for a specified generating family `g`. -/
def evalWord {G : Type*} [Group G] {n : ℕ} (g : Fin n → G) (w : Word n) : G :=
  (w.map fun l => if l.2 then g l.1 else (g l.1)⁻¹).prod

/-- `g : Fin n → G` is a (finite) generating family of `G`. -/
def IsGeneratingFamily {G : Type*} [Group G] {n : ℕ} (g : Fin n → G) : Prop :=
  Subgroup.closure (Set.range g) = ⊤

/-- The word problem for `G` with respect to the specified finite generating family `g` is
decidable: some algorithm answers, for every word, whether it represents the identity.
"Algorithm" is read as Mathlib's `ComputablePred` (partial recursive decision procedure on the
Primcodable encoding of words). -/
def WordProblemDecidableFor {G : Type*} [Group G] {n : ℕ} (g : Fin n → G) : Prop :=
  ComputablePred fun w : Word n => evalWord g w = 1

/-- `G` has decidable word problem: there is a finite generating set for which the word problem
is decidable. -/
def HasDecidableWordProblem (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (g : Fin n → G), IsGeneratingFamily g ∧ WordProblemDecidableFor g

/-- Finitely generated group (written out directly). -/
def IsFinitelyGenerated (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (g : Fin n → G), IsGeneratingFamily g

/-- Finitely presented group: isomorphic to `⟨x₁,…,xₙ | R⟩` with `R` a finite set of relators. -/
def IsFinitelyPresented (H : Type*) [Group H] : Prop :=
  ∃ (n : ℕ) (R : Finset (FreeGroup (Fin n))),
    Nonempty (H ≃* PresentedGroup (R : Set (FreeGroup (Fin n))))

/-- Simple group as in the source: nontrivial, and its only normal subgroups are the identity
subgroup and the whole group. -/
def IsSimple (H : Type*) [Group H] : Prop :=
  Nontrivial H ∧ ∀ N : Subgroup H, N.Normal → N = ⊥ ∨ N = ⊤

/-- `G` embeds (injective group homomorphism) in a finitely presented simple group. -/
def EmbedsInFPSimple (G : Type*) [Group G] : Prop :=
  ∃ (H : Type) (_ : Group H), IsFinitelyPresented H ∧ IsSimple H ∧
    ∃ φ : G →* H, Function.Injective φ

/-- Theorem 1.1. -/
theorem reading_thm_1_1 (G : Type*) [Group G] (hG : IsFinitelyGenerated G) :
    HasDecidableWordProblem G ↔ EmbedsInFPSimple G := sorry

/-- Variant reading of (i): decidable for *every* finite generating set. -/
def HasDecidableWordProblemAll (G : Type*) [Group G] : Prop :=
  ∀ (n : ℕ) (g : Fin n → G), IsGeneratingFamily g → WordProblemDecidableFor g

/-- Theorem 1.1, with (i) read as "for every finite generating set". -/
theorem reading_thm_1_1_all (G : Type*) [Group G] (hG : IsFinitelyGenerated G) :
    HasDecidableWordProblemAll G ↔ EmbedsInFPSimple G := sorry

end ReaderA

/-
AMBIGUITIES AND CHOICES

1. Computability notion. The source says "an algorithm answers this question for every word".
   I use Mathlib's `ComputablePred` (from `Mathlib/Computability/RE.lean`): a predicate on a
   `Primcodable` type is computable iff its Bool-valued indicator is a total computable function
   (Partrec/Turing-equivalent). This is Mathlib's standard notion of a decidable set of codes, so it
   is the closest match to "algorithm answers for every word". Words are `List (Fin n × Bool)`, which
   is Primcodable via `Primcodable.list`, `Primcodable.prod`, `Primcodable.fin`, `Primcodable.bool`.
   I deliberately did NOT use Lean's `Decidable`/`DecidablePred` (that is classical-logic
   decidability and every predicate is "decidable" classically — a junk reading).

2. Words. The source speaks of words "in the generators and their inverses", i.e. arbitrary
   (unreduced) words, so I use lists of letters rather than `FreeGroup (Fin n)` (whose elements are
   reduced words and which is not given a Primcodable instance anyway).

3. Dependence on generating set. The source defines the word problem "for a group with a specified
   finite generating set" and then says "G has decidable word problem" without a set. Main reading:
   there EXISTS a finite generating set with decidable word problem (`reading_thm_1_1`). Since
   decidability is independent of the finite generating set (standard fact), I also give the
   "for every finite generating set" reading (`reading_thm_1_1_all`). Both are claims of the paper
   on the intended reading.

4. Finitely generated. Hypothesis `hG` written directly as existence of a generating family
   `Fin n → G`. (Mathlib's `Group.FG` is equivalent; I wrote my own per the brief.)

5. Finitely presented. Written by hand: `H ≃* PresentedGroup R` for finite `R ⊆ FreeGroup (Fin n)`.

6. Simple. Exactly the source's definition: nontrivial and only normal subgroups are ⊥ and ⊤
   (this matches Mathlib's `IsSimpleGroup`, but written out here).

7. Universe of the simple group. `H : Type` (universe 0). Finitely presented groups are countable,
   so any finitely presented group is isomorphic to one in `Type`; no loss.

8. Embedding = injective group homomorphism, as stated in the source.

9. The constructive remark ("G is supplied with a finite generating set and a word-problem
   decider") is about the proof, not the statement; not formalized.
-/
