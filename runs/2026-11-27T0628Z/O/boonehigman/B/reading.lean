import Mathlib

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
