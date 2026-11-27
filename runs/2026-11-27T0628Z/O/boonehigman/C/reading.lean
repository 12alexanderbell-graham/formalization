import Mathlib

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
