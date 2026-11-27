import Mathlib

open Classical

namespace ReaderC

/-! Definitions written from the source text (abstract and Section 1). -/

/-- Clique minor model of order t: disjoint nonempty connected branch sets, pairwise joined by
an edge. -/
def IsCliqueMinorModel {V : Type} (G : SimpleGraph V) (t : ℕ) (B : Fin t → Set V) : Prop :=
  (∀ i, (B i).Nonempty) ∧
  (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
  (∀ i, (G.induce (B i)).Connected) ∧
  (∀ i j, i ≠ j → ∃ u ∈ B i, ∃ v ∈ B j, G.Adj u v)

/-- h(G): largest order of a clique minor. The set of orders is bounded by |V| and contains 0,
so `sSup` is the maximum. -/
noncomputable def hadwiger {V : Type} (G : SimpleGraph V) : ℕ :=
  sSup {t : ℕ | ∃ B : Fin t → Set V, IsCliqueMinorModel G t B}

/-- A list assignment L is colorable: a proper coloring c with c(v) ∈ L(v) for all v.
Colors are natural numbers; lists are finite sets of colors. -/
def IsLColorable {V : Type} (G : SimpleGraph V) (L : V → Finset ℕ) : Prop :=
  ∃ c : V → ℕ, (∀ v, c v ∈ L v) ∧ ∀ u v, G.Adj u v → c u ≠ c v

/-- ℓ(G) = χ_list(G): least k such that every list assignment with |L(v)| ≥ k is colorable.
The set is nonempty (k = |V| works by greedy coloring) and contains only k ≥ 1 for nonempty V,
so `sInf` is the least such k. -/
noncomputable def listChromatic {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∀ L : V → Finset ℕ, (∀ v, k ≤ (L v).card) → IsLColorable G L}

/-! Readings of the claims. -/

/-- Theorem 1.1: there is an absolute integer C ≥ 1 with ℓ(G) ≤ C·h(G) for every finite
nonempty simple graph G. -/
theorem reading_thm_1_1 :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V),
      listChromatic G ≤ C * hadwiger G := sorry

/-- Corollary 1.2: with the same C as in Theorem 1.1, χ(G) ≤ C·h(G) for every finite nonempty
simple graph G. Stated as: for every C satisfying the Theorem 1.1 bound, the chromatic bound
holds. -/
theorem reading_cor_1_2 :
    ∀ C : ℕ, (∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V),
        listChromatic G ≤ C * hadwiger G) →
      ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V),
        G.chromaticNumber ≤ ((C * hadwiger G : ℕ) : ℕ∞) := sorry

end ReaderC

/-
AMBIGUITIES AND CHOICES (reader C, family O42 listhadwiger)

1. Clique minor and h(G): same model as in the hadwiger file: t nonempty, disjoint, connected
   branch sets (G.induce) pairwise joined by an edge. h(G) is sSup over such t, bounded by |V|
   and containing 0, so it is the true maximum for finite V.
2. List chromatic number ℓ(G): I write it with lists as Finset ℕ (finite color sets) and a
   proper coloring c : V → ℕ with c(v) ∈ L(v). ℓ(G) is sInf of k such that every assignment with
   |L(v)| ≥ k is colorable. For nonempty finite V this set contains |V| (greedy), so it is nonempty
   and the sInf is the least such k; the sInf never returns the empty-set junk value.
   Colors are unrestricted naturals (the union of lists is finite, so this is no loss).
3. Theorem 1.1 is ∃ C : ℕ with 1 ≤ C such that ℓ(G) ≤ C·h(G) for every finite nonempty simple
   graph (type V with Fintype and Nonempty). The constant is over ℕ, which is fine since C is an
   integer in the text. Multiplication is in ℕ with no subtraction, so no junk.
4. Corollary 1.2: "with the same C" is encoded as an implication: for every C satisfying the
   Theorem 1.1 bound for all graphs, χ(G) ≤ C·h(G) for all graphs. The chromatic number is
   Mathlib's ℕ∞-valued G.chromaticNumber, compared with the cast of C·h(G) into ℕ∞.
   I did not require C ≥ 1 in the corollary because the implication holds regardless.
5. Mathlib's SimpleGraph has no clique-minor notion, so none of this is taken from Mathlib.
   Classical decidability is opened for the Finset/Sym2 operations.
-/
