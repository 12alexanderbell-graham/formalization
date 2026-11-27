import Mathlib

namespace ReaderA

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
end ReaderA

namespace ReaderB

open Classical

/-- Amenable as in the source (Følner condition): for every finite K and ε > 0 there is a nonempty
finite D with |gD Δ D| < ε |D| for all g ∈ K. Left translation gD = {g * x | x ∈ D}. -/
def IsAmenableFolner (G : Type) [Group G] : Prop :=
  ∀ (K : Finset G) (ε : ℝ), 0 < ε →
    ∃ D : Finset G, D.Nonempty ∧
      ∀ g ∈ K, ((symmDiff (D.image (fun x => g * x)) D).card : ℝ) < ε * (D.card : ℝ)

/-- Finitely presented: G ≅ F(S) / ⟪⟪R⟫⟫ for finite S and finite R ⊆ F(S). -/
def IsFinitelyPresentedGroup (G : Type) [Group G] : Prop :=
  ∃ (S : Type) (_ : Fintype S) (R : Finset (FreeGroup S)),
    Nonempty (G ≃* (FreeGroup S ⧸ Subgroup.normalClosure (R : Set (FreeGroup S))))

theorem reading :
    ∃ (G : Type) (_ : Group G),
      Infinite G ∧ IsFinitelyPresentedGroup G ∧ IsSimpleGroup G ∧ IsAmenableFolner G := sorry

/-
Ambiguities and choices.
* Amenability: defined by the Følner condition given in the source, not Mathlib's notion; D ranges
  over `Finset G`, K over `Finset G`, ε real > 0, strict inequality, symmetric difference
  `symmDiff` of finsets, gD as image under left multiplication (only left is stated in source).
  With K empty it is trivially satisfied by D nonempty; no junk issue.
* Simple: Mathlib `IsSimpleGroup` (nontrivial, only normal subgroups ⊥ and ⊤). The source's wording
  "only trivial and G" would allow the trivial group, but infiniteness excludes it anyway.
* Finitely presented: finite generating type S (Fintype), finite set of relators R in the free group
  (the "relator words"), iso (MulEquiv) with the quotient by the normal closure. Source says
  "finite sets of generators S and relator words R": R taken as a subset of F(S).
* "Discrete group": no topology; plain `Group`.
* Infinite: `Infinite G`. Universe fixed at Type (0); G is countable anyway as f.p.
-/
end ReaderB

namespace ReaderC

open Classical

/-- The left translate `g D = {g d : d ∈ D}` of a finite set `D` in a group. -/
noncomputable def leftTranslate {G : Type} [Group G] (g : G) (D : Finset G) : Finset G :=
  D.image (fun x => g * x)

/-- Amenable (Følner condition, as in the source): for every finite `K ⊆ G` and every
`ε > 0` there is a nonempty finite `D ⊆ G` with `|g D △ D| < ε |D|` for all `g ∈ K`.
The symmetric difference is written as `(gD \ D) ∪ (D \ gD)`. -/
def Amenable (G : Type) [Group G] : Prop :=
  ∀ (K : Finset G) (ε : ℝ), 0 < ε →
    ∃ D : Finset G, D.Nonempty ∧
      ∀ g ∈ K,
        (((leftTranslate g D \ D) ∪ (D \ leftTranslate g D)).card : ℝ) < ε * (D.card : ℝ)

/-- Simple: the only normal subgroups are the trivial subgroup `⊥` and the whole group `⊤`. -/
def IsSimpleGroup' (G : Type) [Group G] : Prop :=
  ∀ N : Subgroup G, N.Normal → N = ⊥ ∨ N = ⊤

/-- Finitely presented: `G ≅ F(S) / ⟪R⟫` for a finite generating type `S` and a finite set
`R` of relator words in the free group on `S`. -/
def FinitelyPresented (G : Type) [Group G] : Prop :=
  ∃ (S : Type) (_ : Finite S) (R : Set (FreeGroup S)), R.Finite ∧
    Nonempty (G ≃* (FreeGroup S ⧸ Subgroup.normalClosure R))

/-- Theorem 1.1: there exists an infinite, finitely presented, simple, amenable group. -/
theorem reading :
    ∃ (G : Type) (_ : Group G), Infinite G ∧ IsSimpleGroup' G ∧ Amenable G ∧ FinitelyPresented G := sorry

/-
AMBIGUITY NOTES (amenable, C reader)

1. "Discrete group": taken as a plain group with no topology (the Følner condition only
   involves finite sets, so discreteness is automatic).
2. Amenability: quantified over `K : Finset G`, `ε : ℝ` with `0 < ε`, and `D : Finset G` with
   `D.Nonempty`. "Finite" is encoded by `Finset`. The inequality is strict as in the source.
3. Symmetric difference `gD △ D` is written as `(gD \ D) ∪ (D \ gD)`, whose card equals the
   card of the Mathlib symmetric difference; I avoided relying on a Finset `symmDiff` instance.
   Cardinalities are cast to `ℝ` so `ε * |D|` is real. `|D| ≥ 1` by nonemptiness, so no
   division appears (no junk).
4. Left translation `g D`: `D.image (g * ·)`, the left action in the source's `gD`.
5. Simple: "only normal subgroups are the trivial group and G" read literally as
   `N = ⊥ ∨ N = ⊤` for every normal `N`. The source does not add nontriviality of G; it is
   implied in the theorem by `Infinite G`, which excludes the trivial group.
6. Finitely presented: "G ≅ F(S)/⟨⟨R⟩⟩ for finite sets S and R". `S` is a `Type` with
   `Finite S` (finite generating set); `R : Set (FreeGroup S)` with `R.Finite`
   (relator words). `⟪R⟫` is `Subgroup.normalClosure R`. Group isomorphism is `≃*`, and the
   `Nonempty` wrapper makes it a proposition. The quotient uses Mathlib's `⧸` on a normal
   subgroup (the normal closure).
7. Universe: the group is in `Type`. Lean 4 does not accept `∃ (G : Type) [Group G], ...`,
   so the group structure is an ordinary existential binder `(_ : Group G)`; local class-typed
   hypotheses are used as instances, so the predicates see it.
8. "Infinite": `Infinite G`. Together with simplicity this is the requested existence.
9. The predicates `Amenable`, `IsSimpleGroup'`, `FinitelyPresented` are written by me from
   the source's wording; `IsSimpleGroup'` has a prime only to avoid clashing with Mathlib's
   `IsSimpleGroup`.
-/
end ReaderC
