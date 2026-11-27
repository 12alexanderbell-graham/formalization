import Mathlib

/-! Blind readings A, B, C (code unchanged; only `import Mathlib` hoisted). -/

-- ===== reader A =====

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

-- ===== reader B =====

open Set Topology

namespace ReaderB

/-- A classifying complex for `H` on a CW complex `X` (with the whole space as complex):
connected, finitely many cells in every dimension, π₁ ≅ H, and some covering space of `X` is contractible
(this covering is then the universal cover). -/
def IsFiniteClassifying (X : Type) [TopologicalSpace X] [CWComplex (univ : Set X)]
    (H : Type) [Group H] : Prop :=
  ConnectedSpace X ∧
  (∀ n : ℕ, Finite (Topology.CWComplex.cell (univ : Set X) n)) ∧
  (∃ x : X, Nonempty (FundamentalGroup X x ≃* H)) ∧
  (∃ (Y : Type) (_ : TopologicalSpace Y) (p : Y → X), IsCoveringMap p ∧ ContractibleSpace Y)

/-- H has type F∞. -/
def TypeFInfty (H : Type) [Group H] : Prop :=
  ∃ (X : Type) (_ : TopologicalSpace X) (_ : CWComplex (univ : Set X)), IsFiniteClassifying X H

/-- Recursively presented: finitely many generators, relators an r.e. set of words in the generators
(and their inverses), G ≅ ⟨gens | relators⟩ via a surjection from the free group whose kernel is the
normal closure of the relators. -/
def RecursivelyPresented (G : Type) [Group G] : Prop :=
  ∃ (n : ℕ) (φ : FreeGroup (Fin n) →* G), Function.Surjective φ ∧
    ∃ S : Set (List (Fin n × Bool)), REPred (fun w : List (Fin n × Bool) => w ∈ S) ∧
      φ.ker = Subgroup.normalClosure (FreeGroup.mk '' S)

theorem reading_thm_1_1 :
    ∃ (H : Type) (_ : Group H), TypeFInfty H ∧
      ∀ (G : Type) [Group G], Group.IsFinitelyPresented G → ∃ f : G →* H, Function.Injective f :=
  sorry

theorem reading_cor_1_2 :
    ∃ (H : Type) (_ : Group H), TypeFInfty H ∧
      (∀ (G : Type) [Group G], Group.IsFinitelyPresented G → ∃ f : G →* H, Function.Injective f) ∧
      ∀ (G : Type) [Group G], Group.FG G →
        ((∃ f : G →* H, Function.Injective f) ↔ RecursivelyPresented G) :=
  sorry

end ReaderB

/-
Ambiguities / choices
- Mathlib has `CWComplex C` for C ⊆ X; I take X the whole space (`univ`). Its `cell C n : Type` is the
  index type of n-cells; "finitely many cells in each dimension" = `Finite (cell univ n)` for every n.
  Mathlib's CWComplex has weak topology and closure-finiteness built in, matching the usual definition.
- "Contractible universal cover": there is a covering map p : Y → X (`IsCoveringMap`) with Y contractible.
  Such Y is automatically the universal cover (connected, simply connected). I avoid constructing the
  universal cover explicitly. Y is in Type (universe 0) and not required to carry a CW structure.
- Fundamental group: π₁(X,x) ≅ H as groups for some basepoint x (X connected so basepoint irrelevant).
- Universe: all groups and spaces are in Type 0. Finitely presented groups of larger universes are not
  covered; groups there are countable-generated anyway so this seems harmless, but it is a restriction.
- Finitely presented: Mathlib's `Group.IsFinitelyPresented`.
- Recursively presented: Mathlib has no such notion. Encoded relators as words `List (Fin n × Bool)`
  (letter, inverse flag), which is `Primcodable`, and r.e. via `REPred`. Relators are words (not
  necessarily reduced), mapped by `FreeGroup.mk`. Generator count n is part of the existential.
  G = F/⟨⟨R⟩⟩ is expressed via a surjection φ with ker φ = normal closure of R.
- Corollary 1.2 refers to the H of Theorem 1.1, so it is stated jointly with the same H (∃ H such that
  F∞, all f.p. groups embed, and the iff for finitely generated G). Finitely generated: `Group.FG`.
- Junk: none expected; Group instance of H is an existentially quantified structure, not a default.
-/

-- ===== reader C =====

/-!
Reading of O19 (finfty), from `introduction.tex` lines 1-23 only.
-/

open Set Filter

namespace ReaderC

namespace FInfty

/-- A connected CW complex `X` (with the CW structure on all of `X`) that has finitely many
cells in each dimension, with fundamental group `H` (at some basepoint), and whose universal
cover is contractible. The universal cover is a covering map `p : Y → X` whose total space `Y`
is contractible. -/
def IsTypeFInfty (H : Type) [Group H] : Prop :=
  ∃ (X : Type) (_ : TopologicalSpace X),
    ConnectedSpace X ∧
    (∃ inst : Topology.CWComplex (Set.univ : Set X),
      ∀ n : ℕ, Finite (@Topology.CWComplex.cell X _ Set.univ inst n)) ∧
    (∃ x0 : X, Nonempty (FundamentalGroup X x0 ≃* H)) ∧
    ∃ (Y : Type) (_ : TopologicalSpace Y) (p : Y → X),
      IsCoveringMap p ∧ ContractibleSpace Y

/-- `G` is finitely presented: `G ≅ ⟨x_1, …, x_n | R⟩` with `R` a finite set of relators. -/
def IsFinitelyPresented (G : Type) [Group G] : Prop :=
  ∃ (n : ℕ) (R : Finset (FreeGroup (Fin n))),
    Nonempty (G ≃* PresentedGroup (R : Set (FreeGroup (Fin n))))

/-- `G` is finitely generated. -/
def IsFinitelyGenerated (G : Type) [Group G] : Prop :=
  ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤

/-- `G` is recursively presented: `G ≅ ⟨x_1, …, x_n | R⟩` for some `n`, where the relator
set `R` is recursively enumerable. Words are encoded as lists of `(generator, sign)` pairs,
`Primcodable` gives the standard effective encoding. -/
def IsRecursivelyPresented (G : Type) [Group G] : Prop :=
  ∃ (n : ℕ) (R : Set (List (Fin n × Bool))),
    REPred (fun w : List (Fin n × Bool) => w ∈ R) ∧
    Nonempty (G ≃* PresentedGroup (FreeGroup.mk '' R))

/-- Theorem 1.1 (reading): there exists a group `H` of type `F∞` such that every finitely
presented group admits an injective homomorphism into `H`. -/
theorem reading_finfty_universal :
    ∃ (H : Type) (_ : Group H), IsTypeFInfty H ∧
      ∀ (G : Type) [Group G], IsFinitelyPresented G →
        ∃ f : G →* H, Function.Injective f := by
  sorry

/-- Corollary 1.2 (reading): for the group `H` of Theorem 1.1 (any `H` of type `F∞` with the
universal property), a finitely generated group embeds in `H` iff it is recursively
presented. -/
theorem reading_finfty_recursive (H : Type) [Group H] (hH : IsTypeFInfty H)
    (huniv : ∀ (G : Type) [Group G], IsFinitelyPresented G →
      ∃ f : G →* H, Function.Injective f) :
    ∀ (G : Type) [Group G], IsFinitelyGenerated G →
      ((∃ f : G →* H, Function.Injective f) ↔ IsRecursivelyPresented G) := by
  sorry

end FInfty

end ReaderC

/-!
Ambiguities and choices (O19, finfty):

1. Type F∞. The source says: a classifying complex is a connected CW complex with the given
   fundamental group and contractible universal cover, and the group has type F∞ if it admits
   one such complex with finitely many cells in every dimension.
   - "Connected CW complex": Mathlib's `Topology.CWComplex (Set.univ : Set X)` on the whole space `X`,
     plus `ConnectedSpace X`.
   - "finitely many cells in every dimension": `Finite` of the cell index type in each
     dimension `n`, via `Topology.CWComplex.cell`.
   - "fundamental group H": `FundamentalGroup X x0 ≃* H` for some basepoint `x0`. Mathlib's
     `FundamentalGroup` is the endomorphism group of the basepoint in the fundamental groupoid.
   - "contractible universal cover": a covering map `p : Y → X` (`IsCoveringMap`) whose total
     space `Y` is `ContractibleSpace`. A covering with simply connected total space is
     universal. Contractible implies simply connected, so this is the source's universal cover.
   Choice: the universal cover is existentially quantified. This is faithful, since the
   universal cover is unique up to homeomorphism once it exists.
2. Type F_n and the "infinitely many dimensions" remark are not formalised, since the theorem
   does not use them. The source remarks "it may have infinitely many dimensions", which my
   `Topology.CWComplex` (indexed over all `n : ℕ`) allows.
3. "Finitely presented": the source does not define it. I used the standard definition: `G` is
   isomorphic to `PresentedGroup R` for a finite `R ⊂ FreeGroup (Fin n)`. Mathlib has no
   `FinitelyPresented` predicate I could find, so this is my definition.
4. "Embeds" means an injective group homomorphism `G →* H`, as the source's "injective
   homomorphism" says.
5. "Finitely generated": `∃ S : Finset G, closure S = ⊤`. Mathlib's `Group.FG` name is not
   used, to keep the definition literal.
6. Recursively presented: I follow the source's words, "admits a presentation on finitely many
   generators with a recursively enumerable set of relators". The relator set `R` is a set of
   words `List (Fin n × Bool)`, which `Primcodable` encodes. It is required to be recursively
   enumerable via Mathlib's `REPred` (domain of a partial recursive function). The group is
   `PresentedGroup (FreeGroup.mk '' R)`. The words are encoded through `FreeGroup.mk`, so
   non-reduced words are allowed, as they are in a presentation. Mathlib has no
   "recursively presented group" predicate, so this is my definition.
7. Corollary 1.2 refers to "the" `H` from Theorem 1.1. I formalised it as a statement about an
   arbitrary `H` of type `F∞` with the universal property (`huniv`), which is the hypothesis
   the corollary relies on. A standalone `H` is not built here.
8. The corollary is `sorry`. The theorem is `sorry`. Nothing else is `sorry`.
-/
