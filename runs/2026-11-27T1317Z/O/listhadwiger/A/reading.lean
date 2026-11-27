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
