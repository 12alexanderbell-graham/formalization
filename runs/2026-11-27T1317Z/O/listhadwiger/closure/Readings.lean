import Mathlib

namespace ReaderA

variable {V : Type*} [Fintype V]

/-- `G` has a clique minor of order `t`: `t` pairwise disjoint vertex sets, each inducing a
connected (hence nonempty) subgraph, with an edge between every two of them. -/
def HasCliqueMinor (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ B : Fin t → Set V,
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
    (∀ i, (G.induce (B i)).Connected) ∧
    (∀ i j, i ≠ j → ∃ u ∈ B i, ∃ v ∈ B j, G.Adj u v)

open Classical in
/-- `h(G)`: the largest order of a clique minor. Disjoint nonempty branch sets force `t ≤ |V|`,
so `findGreatest` up to `|V|` is the genuine maximum (`t = 0` always qualifies). -/
noncomputable def hadwiger (G : SimpleGraph V) : ℕ :=
  Nat.findGreatest (HasCliqueMinor G) (Fintype.card V)

open Classical in
/-- Chromatic number as a natural number (exists since `G` is `|V|`-colorable; no `⊤`). -/
noncomputable def chromatic (G : SimpleGraph V) : ℕ :=
  Nat.find (⟨Fintype.card V, G.colorable_of_fintype⟩ : ∃ n, G.Colorable n)

/-- An `L`-coloring: a proper coloring `c` with `c v ∈ L v` at every vertex.
Colors are natural numbers. -/
def IsLColoring (G : SimpleGraph V) (L : V → Finset ℕ) (c : V → ℕ) : Prop :=
  (∀ v, c v ∈ L v) ∧ ∀ u v, G.Adj u v → c u ≠ c v

/-- Every list assignment with all lists of size `≥ k` admits an `L`-coloring. -/
def ListColorableWith (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, k ≤ (L v).card) → ∃ c : V → ℕ, IsLColoring G L c

/-- Lists of size `≥ |V|` always admit an `L`-coloring (Hall: pick distinct colors). This
makes the `Nat.find` below well-defined, so `ℓ(G)` carries no junk value. -/
theorem listColorableWith_card (G : SimpleGraph V) :
    ListColorableWith G (Fintype.card V) := by
  classical
  intro L hL
  obtain ⟨f, hf, hfL⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective L).1 (by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · simp
    · calc s.card ≤ Fintype.card V := Finset.card_le_univ s
        _ ≤ (L v).card := hL v
        _ ≤ (s.biUnion L).card := Finset.card_le_card (Finset.subset_biUnion_of_mem L hv))
  exact ⟨f, hfL, fun u v huv h => G.ne_of_adj huv (hf h)⟩

open Classical in
/-- List chromatic number `ℓ(G)`: the least `k` such that every assignment with
`|L(v)| ≥ k` is colorable. -/
noncomputable def listChromatic (G : SimpleGraph V) : ℕ :=
  Nat.find (⟨Fintype.card V, listColorableWith_card G⟩ : ∃ k, ListColorableWith G k)

/-- Theorem 1.1: there is an absolute integer `C ≥ 1` such that every finite nonempty simple
graph `G` satisfies `ℓ(G) ≤ C · h(G)`. -/
theorem reading_thm_1_1 :
    ∃ C : ℕ, 1 ≤ C ∧
      ∀ (W : Type) [Fintype W] [Nonempty W] (G : SimpleGraph W),
        listChromatic G ≤ C * hadwiger G := sorry

/-- Corollary 1.2: with the same constant `C` as in Theorem 1.1, `χ(G) ≤ C · h(G)` for every
finite nonempty simple graph. Stated as: one `C ≥ 1` that works for both. -/
theorem reading_cor_1_2 :
    ∃ C : ℕ, 1 ≤ C ∧
      (∀ (W : Type) [Fintype W] [Nonempty W] (G : SimpleGraph W),
        listChromatic G ≤ C * hadwiger G) ∧
      (∀ (W : Type) [Fintype W] [Nonempty W] (G : SimpleGraph W),
        chromatic G ≤ C * hadwiger G) := sorry

end ReaderA

/-
AMBIGUITIES AND CHOICES (reader A)

1. Clique minor / `h(G)`: branch-set definition taken from the intro's own description
   ("vertices represented by disjoint connected sets, and every two sets have an edge between
   them"). Connectedness via Mathlib `(G.induce (B i)).Connected`, which includes nonemptiness.
   `h` is `Nat.findGreatest` up to `|V|`; since `t ≤ |V|` for any clique minor this is the true
   maximum, and `t = 0` always qualifies (no sSup / empty-set junk). For nonempty `G`, `h ≥ 1`.

2. Color set: the text says "a finite set of colors" without fixing a universe of colors. I take
   colors in `ℕ`. Since `V` is finite, any list assignment over an arbitrary color type uses
   finitely many colors and can be relabelled injectively into `ℕ`, so nothing is lost. The text
   stresses the constant is independent of the number of colors; quantifying over all
   `L : V → Finset ℕ` captures that.

3. `ℓ(G)` "least integer k for which every assignment with |L(v)| ≥ k is colorable": defined by
   `Nat.find`, with existence *proved* (`listColorableWith_card`, via Hall's theorem: lists of
   size ≥ |V| admit an injective choice, which is proper because adjacent vertices are distinct).
   So `ℓ` is never a junk value; it is a genuine least element. (k = 0 never qualifies for
   nonempty V, since then the empty list is allowed.)

4. Chromatic number: `Nat.find` on Mathlib's `Colorable`, existence by `|V|`; avoids the `ℕ∞`
   `chromaticNumber` and its `⊤`.

5. "absolute integer C ≥ 1": `C : ℕ` with `1 ≤ C` (an integer ≥ 1 is a natural number).
   Graphs quantified over `W : Type` with `[Fintype W] [Nonempty W]` (universe fixed at `Type`).

6. Corollary 1.2 "with the constant C in Theorem 1.1": rendered as the existence of a single
   `C ≥ 1` satisfying both the list bound and the ordinary bound, so "same C" is enforced.
   (The alternative reading "every C valid for Thm 1.1 also works" is a weaker-looking but
   trivially-equivalent-to-χ ≤ ℓ statement; I chose the conjunction.)

7. No ℕ subtraction or division appears; `C * h G` is ℕ multiplication.
-/

namespace ReaderB

open SimpleGraph

def HasCliqueMinor {V : Type} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ B : Fin t → Set V, (∀ i, (B i).Nonempty) ∧ (∀ i, (G.induce (B i)).Connected) ∧
    Pairwise (Function.onFun Disjoint B) ∧
    ∀ i j, i ≠ j → ∃ u ∈ B i, ∃ v ∈ B j, G.Adj u v

/-- `h` is the Hadwiger number (largest clique-minor order). -/
def IsHadwigerNumber {V : Type} (G : SimpleGraph V) (h : ℕ) : Prop :=
  HasCliqueMinor G h ∧ ∀ t, HasCliqueMinor G t → t ≤ h

/-- Every list assignment with all lists of size ≥ k admits a proper coloring from the lists. -/
def ListColorable {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (κ : Type) (L : V → Finset κ), (∀ v, k ≤ (L v).card) →
    ∃ c : V → κ, (∀ v, c v ∈ L v) ∧ ∀ u v, G.Adj u v → c u ≠ c v

/-- `ℓ` is the list chromatic number: least k such that G is k-list-colorable. -/
def IsListChromaticNumber {V : Type} (G : SimpleGraph V) (ℓ : ℕ) : Prop :=
  ListColorable G ℓ ∧ ∀ k, k < ℓ → ¬ ListColorable G k

/-- The statement of Theorem 1.1 for a given constant. -/
def ListBound (C : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) (ℓ h : ℕ),
    IsListChromaticNumber G ℓ → IsHadwigerNumber G h → ℓ ≤ C * h

/-- The conclusion of Corollary 1.2 for a given constant. -/
def OrdinaryBound (C : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) (h : ℕ),
    IsHadwigerNumber G h → G.chromaticNumber ≤ ((C * h : ℕ) : ℕ∞)

theorem reading_thm_1_1 : ∃ C : ℕ, 1 ≤ C ∧ ListBound C := sorry

theorem reading_cor_1_2 : ∀ C : ℕ, 1 ≤ C → ListBound C → OrdinaryBound C := sorry

/-
Ambiguities / choices
- h(G): as in the other family; branch sets Fin t → Set V; `IsHadwigerNumber` = attained + upper bound
  (no sSup). Exists for finite nonempty G.
- ℓ(G): "least k such that every assignment with |L(v)| ≥ k is colorable": `IsListChromaticNumber`
  = k-choosable and not (k-1)-choosable-style (¬ for every smaller k), avoiding sInf. For finite nonempty G
  it exists (k = |V| works). Color type κ : Type is universally quantified (universe 0; finite lists, so
  WLOG). "Finite set of colors" = Finset κ. Lists of size ≥ k (not exactly k).
- χ(G): Mathlib `chromaticNumber : ℕ∞`; the corollary bounds it in ℕ∞ by the cast of C*h (no toNat/⊤ junk).
  The proof remark χ ≤ ℓ is not stated; Corollary 1.2 is stated as "any C satisfying Theorem 1.1's conclusion
  also gives χ ≤ C h", matching "with the constant C in Theorem 1.1" (hypothesis `1 ≤ C` kept for fidelity).
- C is ℕ ("absolute integer C ≥ 1"); C·h is ℕ multiplication, no subtraction.
- Graphs: V : Type finite nonempty, simple (SimpleGraph).
-/

end ReaderB

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
