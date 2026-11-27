import Mathlib

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
