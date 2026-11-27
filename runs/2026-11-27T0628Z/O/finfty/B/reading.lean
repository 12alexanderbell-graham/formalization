import Mathlib

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
