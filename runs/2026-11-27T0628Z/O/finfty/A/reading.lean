import Mathlib

namespace ReaderA

open Topology

/-- A *classifying complex* for a group `H`, in the source's words: a connected CW complex with
fundamental group `H` and contractible universal cover. Here the CW complex is the whole
(Hausdorff) space `X`, i.e. `Set.univ` carries a Mathlib `Topology.CWComplex` structure
(cells of every dimension `n : ℕ` are allowed, so it "may have infinitely many dimensions").
The universal cover is a covering map `p : Y → X` (continuous, surjective) with `Y` contractible
(contractible implies simply connected, so this is a universal cover). -/
def IsClassifyingComplex (H : Type) [Group H] (X : Type) [TopologicalSpace X]
    (_cw : CWComplex (Set.univ : Set X)) : Prop :=
  ConnectedSpace X ∧
    (∃ x₀ : X, Nonempty (FundamentalGroup X x₀ ≃* H)) ∧
    ∃ (Y : Type) (_ : TopologicalSpace Y) (p : Y → X),
      Continuous p ∧ IsCoveringMap p ∧ Function.Surjective p ∧ ContractibleSpace Y

/-- `H` has type `F∞`: it admits one classifying complex with finitely many cells in every
dimension. -/
def TypeFInfty (H : Type) [Group H] : Prop :=
  ∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (cw : CWComplex (Set.univ : Set X)),
    (∀ n : ℕ, Finite (Topology.CWComplex.cell (Set.univ : Set X) n)) ∧
    IsClassifyingComplex H X cw

/-- `G` is finitely presented: `G ≅ ⟨x₁,…,xₙ | R⟩` with finitely many generators and a finite set
`R` of relators. -/
def FinitelyPresented (G : Type) [Group G] : Prop :=
  ∃ (n : ℕ) (R : Finset (FreeGroup (Fin n))),
    Nonempty (G ≃* PresentedGroup (R : Set (FreeGroup (Fin n))))

/-- `G` is recursively presented: it admits a presentation on finitely many generators
`x₁,…,xₙ` with a recursively enumerable set of relators. Relators are words, i.e. lists of
(generator, exponent sign) pairs `List (Fin n × Bool)` (as in Mathlib's `FreeGroup.mk`),
which carry a standard `Primcodable` encoding; "recursively enumerable" is Mathlib's `REPred`
(the domain of a partial recursive function). -/
def RecursivelyPresented (G : Type) [Group G] : Prop :=
  ∃ (n : ℕ) (W : Set (List (Fin n × Bool))),
    REPred (fun w => w ∈ W) ∧
    Nonempty (G ≃* PresentedGroup (FreeGroup.mk '' W))

/-- `G` embeds in `H`: there is an injective homomorphism `G → H`. -/
def EmbedsIn (G : Type) [Group G] (H : Type) [Group H] : Prop :=
  ∃ φ : G →* H, Function.Injective φ

/-- Theorem 1.1: there exists a group `H` of type `F∞` such that every finitely presented group
admits an injective homomorphism into `H`. -/
theorem reading_thm_1_1 :
    ∃ (H : Type) (_ : Group H), TypeFInfty H ∧
      ∀ (G : Type) [Group G], FinitelyPresented G → EmbedsIn G H := sorry

/-- Corollary 1.2, for "`H`" being any group as in Theorem 1.1: a finitely generated group embeds
in `H` if and only if it is recursively presented. -/
theorem reading_cor_1_2 (H : Type) [Group H] (_hH : TypeFInfty H)
    (_huniv : ∀ (G : Type) [Group G], FinitelyPresented G → EmbedsIn G H)
    (G : Type) [Group G] [Group.FG G] :
    EmbedsIn G H ↔ RecursivelyPresented G := sorry

/-- Theorem 1.1 and Corollary 1.2 together, for one and the same `H`. -/
theorem reading_thm_1_1_and_cor_1_2 :
    ∃ (H : Type) (_ : Group H), TypeFInfty H ∧
      (∀ (G : Type) [Group G], FinitelyPresented G → EmbedsIn G H) ∧
      (∀ (G : Type) [Group G], Group.FG G → (EmbedsIn G H ↔ RecursivelyPresented G)) := sorry

end ReaderA

/-
Ambiguities and choices (Reader A, O19 finfty):

1. CW complex: Mathlib's classical `Topology.CWComplex` on a subset C of a space X; I take
   C = Set.univ (the whole space is the complex) and add `T2Space X` since CW complexes are
   Hausdorff in the classical definition (Mathlib's class does not itself include T2). Cells
   are indexed by every n : ℕ, so infinitely many dimensions are allowed, as the source says.
   "Finitely many cells in every dimension": ∀ n, Finite (cell n). (Mathlib's
   `CWComplex.FiniteType` says the same; I wrote it out.)

2. Classifying complex: "connected CW complex with the given fundamental group and contractible
   universal cover". Connected: `ConnectedSpace X`. Fundamental group: for some base point x₀,
   π₁(X, x₀) ≃* H (for a connected CW complex, which is path-connected, the choice of x₀ does not
   matter up to isomorphism; ∃ x₀ also guarantees X nonempty). Universal cover: a covering map
   p : Y → X (Mathlib `IsCoveringMap`, plus `Continuous` and `Surjective`, since Mathlib's
   covering maps may have empty fibres) with Y contractible (`ContractibleSpace`, which makes Y
   nonempty, path-connected and simply connected, hence p is a universal cover). I do not
   separately require Y simply connected, as contractible implies it.

3. Universes: H, X, Y and the test groups G all live in `Type` (universe 0). Groups of type F∞
   and finitely presented / finitely generated groups are countable, so nothing is lost up to
   isomorphism; quantifying over `G : Type` covers all of them up to isomorphism.

4. "Type F_n" and "F_2 ⇔ finitely presented" are background in the source, not claims; they are
   not formalized. Only type F∞ is defined.

5. Finitely presented: defined by me as G ≃* ⟨Fin n | R⟩ with R a Finset of the free group
   (Mathlib's `PresentedGroup`), rather than using any library predicate.

6. Recursively presented (Mathlib has no such notion): "a presentation on finitely many
   generators with a recursively enumerable set of relators". Generators Fin n; relators are a
   set W of words in List (Fin n × Bool) (the letter x_i^{±1}), r.e. in the sense of Mathlib's
   `REPred` w.r.t. the canonical `Primcodable` encoding of lists of pairs; the group is
   ⟨Fin n | image of W in the free group⟩. Using words rather than free-group elements avoids
   having to choose an encoding of the free group itself; r.e.-ness of a set of words vs. of
   its set of reduced forms are equivalent notions of presentation up to changing W, so this
   matches the usual definition.

7. "Embeds" / "admits an injective homomorphism into H": ∃ φ : G →* H injective.

8. Corollary 1.2 says "embeds in H" for the H of Theorem 1.1. I state it for every H having the
   properties in Theorem 1.1 (`reading_cor_1_2`, hypotheses: type F∞ and universal for finitely
   presented groups) and, separately, as an existence statement bundled with Theorem 1.1 for one
   and the same H (`reading_thm_1_1_and_cor_1_2`). "Finitely generated" is Mathlib's
   `Group.FG`.

9. No junk values: all notions are Props built from existentials; nothing uses sSup, division
   or default values.
-/
