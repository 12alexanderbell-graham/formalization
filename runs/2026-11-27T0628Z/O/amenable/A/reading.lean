import Mathlib

/-!
# Blind reading (reader A): family O13, infinite finitely presented simple amenable group

Source: `amenable/sources/introduction_lines1-20.tex`, Theorem 1.1 (`thm:main`).
-/

open Classical

namespace O13Reading

/-- "A discrete group `G` is amenable if, for every finite `K ⊆ G` and every `ε > 0`,
there is a nonempty finite `D ⊆ G` such that `|gD △ D| < ε |D|` for `g ∈ K`."
Here `gD` is the left translate `{g * x | x ∈ D}`. -/
def IsAmenable (G : Type) [Group G] : Prop :=
  ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
    ∃ D : Finset G, D.Nonempty ∧
      ∀ g ∈ K, ((symmDiff (D.image (fun x => g * x)) D).card : ℝ) < ε * (D.card : ℝ)

/-- "It is simple if its only normal subgroups are the trivial group and `G`." -/
def IsSimple (G : Type) [Group G] : Prop :=
  ∀ N : Subgroup G, N.Normal → N = ⊥ ∨ N = ⊤

/-- "finitely presented if `G ≅ F(S)/⟨⟨R⟩⟩` for finite sets of generators `S` and
relator words `R`." `F(S)` is the free group on `S`, `⟨⟨R⟩⟩` the normal closure of `R`. -/
def IsFinitelyPresented (G : Type) [Group G] : Prop :=
  ∃ (S : Type) (_ : Finite S) (R : Set (FreeGroup S)),
    R.Finite ∧ Nonempty (G ≃* (FreeGroup S ⧸ Subgroup.normalClosure R))

/-- Theorem 1.1. There exists an infinite finitely presented simple amenable group. -/
theorem reading :
    ∃ (G : Type) (_ : Group G),
      Infinite G ∧ IsFinitelyPresented G ∧ IsSimple G ∧ IsAmenable G := sorry

end O13Reading

/-
## Ambiguity notes (reader A)

1. "discrete group": an abstract `Group G` with no topology; `G : Type` (universe 0).
   The group is given by an existential over the carrier and the `Group` structure.
2. Amenability is the source's Følner condition, written out by me (not Mathlib's
   measure-theoretic notion). `ε` ranges over positive reals; `K` over finite subsets
   (as `Finset G`, `K` may be empty, which is harmless); `D` must be nonempty and finite.
   `gD` read as the LEFT translate `{g x : x ∈ D}` (`D.image (g * ·)`), matching the
   notation `gD`. The inequality is strict (`<`) as in the source, compared in `ℝ`.
   `|·|` is `Finset.card`. Since `D` is nonempty, `ε |D| > 0`; no division occurs.
3. `△` is set symmetric difference, Lean's `symmDiff` on `Finset G` (decidable equality
   via `open Classical`).
4. Simple: "its only normal subgroups are the trivial group and G" read as: every normal
   subgroup is `⊥` or `⊤`. This reading does not demand `⊥ ≠ ⊤` (it would admit the
   trivial group), unlike Mathlib's `IsSimpleGroup`, which requires nontriviality. The
   difference is immaterial here because the theorem also demands `Infinite G`.
5. Finitely presented: `S` is a finite type (`Finite S`) of generators in universe 0,
   `R` a finite set (`Set.Finite`) of elements of the free group `FreeGroup S`
   ("relator words", read as reduced words = free-group elements), `⟨⟨R⟩⟩` is
   `Subgroup.normalClosure R`, and `≅` is a group isomorphism `≃*` (Nonempty of it).
   I wrote the quotient directly rather than via Mathlib's `PresentedGroup` (which is
   definitionally the same quotient).
6. Infinite: Mathlib's `Infinite G`, i.e. the carrier type is not finite.
7. The four properties are required of one and the same `G` simultaneously.
8. Source hygiene: the source file provided is `introduction_lines1-20.tex` (an
   excerpt), so its sha256 (prefix 8354b3e40e1292ea) cannot be compared with the
   brief's prefix for the full `introduction.tex` (a8b988e030edf9ac).
-/
