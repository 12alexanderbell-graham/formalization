import Mathlib

/-! Blind readings A, B, C (code unchanged; only `import Mathlib` hoisted). -/

-- ===== reader A =====

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

-- ===== reader B =====

namespace ReaderB

/-- A word in `n` generators and their inverses: a list of (generator index, sign) pairs
(`true` = the generator, `false` = its inverse). -/
abbrev Word (n : ℕ) := List (Fin n × Bool)

/-- The element of `G` represented by a word, for a tuple `gens` of generators. -/
def evalWord {G : Type} [Group G] {n : ℕ} (gens : Fin n → G) (w : Word n) : G :=
  (w.map fun a => if a.2 then gens a.1 else (gens a.1)⁻¹).prod

/-- `G` has decidable word problem: for some finite generating tuple `gens`, the set of words
representing the identity is a computable predicate (a Turing-computable decision). -/
def HasDecidableWordProblem (G : Type) [Group G] : Prop :=
  ∃ (n : ℕ) (gens : Fin n → G), Subgroup.closure (Set.range gens) = ⊤ ∧
    ComputablePred fun w : Word n => evalWord gens w = 1

/-- Simple, in the source's sense: nontrivial and only normal subgroups are `⊥` and `⊤`.
(This is Mathlib's `IsSimpleGroup`, restated.) -/
def SourceSimple (H : Type) [Group H] : Prop :=
  Nontrivial H ∧ ∀ N : Subgroup H, N.Normal → N = ⊥ ∨ N = ⊤

theorem reading_boone_higman (G : Type) [Group G] [Group.FG G] :
    HasDecidableWordProblem G ↔
      ∃ (H : Type) (_ : Group H), Group.IsFinitelyPresented H ∧ SourceSimple H ∧
        ∃ f : G →* H, Function.Injective f := sorry

end ReaderB

/-
Ambiguities and choices.
* Word problem is stated for "a specified finite generating set"; independence of the generating set is
  a standard fact, so I existentially quantify over a finite generating tuple (Fin n → G) with n free.
  Since G is FG such tuples exist, so no vacuity; (i) is thus "some (equivalently every) finite generating
  tuple has decidable word problem". Duplicates/identity among gens allowed (harmless).
* Words: List (Fin n × Bool). Decider: Mathlib `ComputablePred` (Turing/partial-recursive computable
  predicate on a Primcodable type; Fin n × Bool and lists are Primcodable). This is "an algorithm answers
  for every word", closest to Church-Turing; ComputablePred is total computable decidability, not just
  semi-decidability. Chosen over `Decidable` (which is noncomputable-friendly and trivial classically).
* Simple: written out as nontrivial + only normal subgroups ⊥,⊤ (equals IsSimpleGroup).
* Finitely presented: Mathlib's `Group.IsFinitelyPresented` (finite generators, finitely many relators).
* Embedding: injective MonoidHom. Universe: G and H both in `Type` (small), no loss for countable groups;
  H quantified in Type (a finitely presented group is countable anyway).
* The implicit hypothesis "G finitely generated" is `Group.FG G`. The remark that in (i)->(ii) G need not
  be finitely presented is automatically accommodated (G is only FG).
* Junk values avoided: no division/partial functions; ComputablePred on words avoids Decidable instance junk.
-/

-- ===== reader C =====

namespace ReaderC

/-! Reading of O32: Theorem 1.1 (Boone-Higman, stated as the equivalence
    "decidable word problem <-> embeds in a finitely presented simple group").

Definitions written from the source:
* A word over generators `g : Fin k → G` is a list of letters `(i, b)`, where `b = true`
  means `g i` and `b = false` means `(g i)⁻¹`. Its value is the product in `G`.
* "Decidable word problem" for a generating tuple `g`: there is a total computable
  (Mathlib `Computable`, i.e. recursive) function `f` on words such that `f w = true`
  exactly when the word `w` has value `1` in `G`.
* "G has decidable word problem": for some finite generating tuple `g` the above holds.
  (Decidability does not depend on the generating set; the source fixes one and the
  choice "some" is the standard, equivalent reading.)
* "Simple": Mathlib's `IsSimpleGroup` (nontrivial, only normal subgroups ⊥ and ⊤).
* "Finitely presented": Mathlib's `Group.IsFinitelyPresented`.
* "Embeds": there is an injective group homomorphism `G →* H`.

Ambiguities and choices:
* Computability notion: Mathlib `Computable` on `List (Fin k × Bool)` (Primcodable),
  which is the standard recursive-function notion for a decider of the word problem.
* The source's constructive direction supplies G with a finite generating set and a decider,
  and says G need not be finitely presented. We do not add any extra hypotheses.
* Universes: G and H live in `Type` (universe 0), matching the source's countable-ish
  setting; no further universe generality is claimed.
-/

/-- Value in `G` of a word over the generating tuple `g`. -/
def wordValue {G : Type} [Group G] {k : ℕ} (g : Fin k → G) (w : List (Fin k × Bool)) : G :=
  (w.map (fun ib => if ib.2 then g ib.1 else (g ib.1)⁻¹)).prod

/-- The word problem for the generating tuple `g` is decidable (recursive decider). -/
def WordProblemDecidable {G : Type} [Group G] {k : ℕ} (g : Fin k → G) : Prop :=
  ∃ f : List (Fin k × Bool) → Bool,
    Computable f ∧ ∀ w : List (Fin k × Bool), f w = true ↔ wordValue g w = 1

/-- Theorem 1.1, both directions, for every finitely generated group `G`. -/
theorem reading_boone_higman_thm11 (G : Type) [Group G] (hG : Group.FG G) :
    (∃ k : ℕ, ∃ g : Fin k → G, Subgroup.closure (Set.range g) = ⊤ ∧ WordProblemDecidable g) ↔
    ∃ (H : Type) (_ : Group H),
      Group.IsFinitelyPresented H ∧ IsSimpleGroup H ∧
        ∃ φ : G →* H, Function.Injective φ := by
  sorry

end ReaderC
