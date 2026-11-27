import Mathlib

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
