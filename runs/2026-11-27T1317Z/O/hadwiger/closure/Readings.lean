import Mathlib

namespace ReaderA

open Finset

variable {V : Type*} [Fintype V]

/-- `G` contains a `K_t` minor: `t` pairwise disjoint branch sets, each inducing a connected
(hence nonempty) subgraph, with an edge of `G` between any two distinct branch sets. -/
def HasCliqueMinor (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ B : Fin t → Set V,
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
    (∀ i, (G.induce (B i)).Connected) ∧
    (∀ i j, i ≠ j → ∃ u ∈ B i, ∃ v ∈ B j, G.Adj u v)

open Classical in
/-- Hadwiger number `h(G)`: the largest `t` such that `G` has a `K_t` minor.
Branch sets are disjoint and nonempty, so `t ≤ |V|`; hence `findGreatest` up to `|V|`
is the genuine maximum (and `t = 0` always qualifies). -/
noncomputable def hadwiger (G : SimpleGraph V) : ℕ :=
  Nat.findGreatest (HasCliqueMinor G) (Fintype.card V)

open Classical in
/-- The family `𝓘(G)` of independent vertex sets. -/
noncomputable def indepSets (G : SimpleGraph V) : Finset (Finset V) :=
  Finset.filter (fun s : Finset V => G.IsIndepSet (↑s : Set V)) Finset.univ

/-- Independence number `α(G)`: maximum size of an independent vertex set
(the empty set is independent, so the maximum over a nonempty finite family). -/
noncomputable def indepNumber (G : SimpleGraph V) : ℕ :=
  (indepSets G).sup Finset.card

open Classical in
/-- Chromatic number `χ(G)` as a natural number: least `n` with a proper `n`-coloring.
Exists since `G` is `|V|`-colorable, so no `⊤` / junk value. -/
noncomputable def chromatic (G : SimpleGraph V) : ℕ :=
  Nat.find (⟨Fintype.card V, G.colorable_of_fintype⟩ : ∃ n, G.Colorable n)

/-- Two disjoint edges `e, f` are touching if some edge of `G` joins their endpoint sets. -/
def Touching (G : SimpleGraph V) (e f : Sym2 V) : Prop :=
  ∃ u ∈ e, ∃ v ∈ f, G.Adj u v

/-- A connected matching: a set of edges of `G`, pairwise disjoint (a matching), and
pairwise touching. -/
def IsConnectedMatching (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v, v ∈ e → v ∉ f) ∧
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f → Touching G e f)

open Classical in
/-- `cm(G)`: maximum size of a connected matching (the empty matching qualifies). -/
noncomputable def cm (G : SimpleGraph V) : ℕ :=
  ((univ : Finset (Finset (Sym2 V))).filter (fun M => IsConnectedMatching G M)).sup
    Finset.card

open Classical in
/-- A fractional coloring: nonnegative weights `w_I` on `I ∈ 𝓘(G)` with
`∑_{I ∋ v} w_I ≥ 1` for every vertex `v` (values of `w` off `𝓘(G)` are ignored). -/
def IsFracColoring (G : SimpleGraph V) (w : Finset V → ℝ) : Prop :=
  (∀ I ∈ indepSets G, 0 ≤ w I) ∧
  ∀ v : V, 1 ≤ ∑ I ∈ (indepSets G).filter (fun I => v ∈ I), w I

/-- Fractional chromatic number `χ_f(G)`: the minimum of `∑_I w_I` over fractional colorings.
The set is nonempty (unit weights on singletons) and bounded below by `0`, so `sInf` is
the genuine infimum (which the paper asserts is a minimum). -/
noncomputable def fracChromatic (G : SimpleGraph V) : ℝ :=
  sInf {r : ℝ | ∃ w : Finset V → ℝ, IsFracColoring G w ∧ r = ∑ I ∈ indepSets G, w I}

/-- Theorem 1.1: there are arbitrarily large integers `m` for which some `m`-vertex finite
simple graph `G` has `α(G) ≤ 2` and `cm(G) < m/100`. -/
theorem reading_thm_1_1 :
    ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ ∃ G : SimpleGraph (Fin m),
      indepNumber G ≤ 2 ∧ (cm G : ℝ) < (m : ℝ) / 100 := sorry

/-- Corollary 1.2: finite nonempty simple graphs of arbitrarily large order `m` with
`h(G) < 26m/75 + 2/3 < m/2 ≤ χ_f(G) ≤ χ(G)`. -/
theorem reading_cor_1_2 :
    ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ 0 < m ∧ ∃ G : SimpleGraph (Fin m),
      (hadwiger G : ℝ) < 26 * (m : ℝ) / 75 + 2 / 3 ∧
      26 * (m : ℝ) / 75 + 2 / 3 < (m : ℝ) / 2 ∧
      (m : ℝ) / 2 ≤ fracChromatic G ∧
      fracChromatic G ≤ (chromatic G : ℝ) := sorry

/-- Hadwiger's conjecture is false: not every finite nonempty simple graph has `h(G) ≥ χ(G)`. -/
theorem reading_hadwiger_false :
    ¬ ∀ (W : Type) [Fintype W] [Nonempty W] (G : SimpleGraph W),
      chromatic G ≤ hadwiger G := sorry

end ReaderA

/-
AMBIGUITIES AND CHOICES (reader A)

1. Minor / Hadwiger number. The text says only "largest t for which G contains a K_t minor".
   I used the branch-set characterisation (as in the companion paper's own phrasing:
   disjoint connected sets, every two joined by an edge). Connectedness is
   `(G.induce (B i)).Connected`, which in Mathlib includes nonemptiness, so empty branch sets
   are excluded. `h` is `Nat.findGreatest` up to `|V|`; since disjoint nonempty branch sets
   force `t ≤ |V|`, this is the true maximum, not a truncation; `t = 0` always qualifies,
   so there is no empty-set junk. No `sSup` used.

2. Matching / connected matching. A matching = finite set of edges of `G` that pairwise share
   no endpoint. "Touching" = some edge of `G` joins a vertex of `e` to a vertex of `f`.
   "Pairwise touching" is required for every pair of distinct matching edges (the text stresses
   this). `cm` = `Finset.sup card` over all qualifying edge sets; the empty set qualifies, so the
   max is over a nonempty family (no junk).

3. Independence number `α` defined by me as max card of a Mathlib `IsIndepSet` finset (Finset
   sup, nonempty family). Did not use Mathlib's `indepNum` (an `sSup`) to avoid any sSup issue.

4. Chromatic number: Mathlib's `chromaticNumber` is `ℕ∞`-valued; I instead take `Nat.find`
   of `G.Colorable n`, with existence witnessed by `|V|`, so no `⊤`.

5. Fractional chromatic number: weights `w : Finset V → ℝ`, only values on `𝓘(G)` matter
   (nonnegativity and the sums range over `𝓘(G)`); the empty independent set is included in
   `𝓘(G)` as in "the family of its independent vertex sets" (harmless). The text says
   "minimum"; I use `sInf` over achievable totals, which is over a nonempty, bounded-below set
   (singleton unit weights are feasible; totals ≥ 0), so it is the genuine infimum; equality with
   the minimum is LP theory and is not needed for the statements. The text defines χ_f only for
   nonempty graphs; Corollary 1.2 includes `0 < m`.

6. "Arbitrarily large integers m" read as: for every `N` there is `m ≥ N`. An "m-vertex graph"
   is taken with vertex type `Fin m` (any finite type of card m is isomorphic). Real-number
   comparisons (`m/100`, `26m/75 + 2/3`, `m/2`) are done in `ℝ` after casting, so no ℕ division
   or subtraction anywhere.

7. Corollary 1.2's chain is stated as four separate real inequalities. The middle inequality
   `26m/75 + 2/3 < m/2` is pure arithmetic (equivalent to m > 100/23, i.e. m ≥ 5), kept for
   literalness. The final "Thus ... fractional weakening χ_f(G) ≤ h(G) is false" is not stated
   separately (it follows from the chain).

8. "Hadwiger's conjecture is false": negation of `∀ finite nonempty simple graph, χ(G) ≤ h(G)`,
   quantified over `W : Type` with `[Fintype W] [Nonempty W]`. Universe fixed at `Type`
   (Theorem/Corollary only need `Fin m`).
-/

namespace ReaderB

open SimpleGraph

/-- `G` has a `K_t` minor: `t` nonempty, pairwise disjoint, connected branch sets, any two joined by an edge. -/
def HasCliqueMinor {V : Type} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ B : Fin t → Set V, (∀ i, (B i).Nonempty) ∧ (∀ i, (G.induce (B i)).Connected) ∧
    Pairwise (Function.onFun Disjoint B) ∧
    ∀ i j, i ≠ j → ∃ u ∈ B i, ∃ v ∈ B j, G.Adj u v

/-- `h` is the Hadwiger number: the largest `t` with a `K_t` minor. -/
def IsHadwigerNumber {V : Type} (G : SimpleGraph V) (h : ℕ) : Prop :=
  HasCliqueMinor G h ∧ ∀ t, HasCliqueMinor G t → t ≤ h

/-- A connected matching: a set of edges of `G`, pairwise disjoint, pairwise touching. -/
def IsConnectedMatching {V : Type} (G : SimpleGraph V) (M : Set (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint {v | v ∈ e} {v | v ∈ f}) ∧
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∃ u ∈ e, ∃ v ∈ f, G.Adj u v)

/-- `c` is `cm(G)`: the maximum cardinality of a (finite) connected matching. -/
def IsCmNumber {V : Type} (G : SimpleGraph V) (c : ℕ) : Prop :=
  (∃ M : Finset (Sym2 V), IsConnectedMatching G (M : Set (Sym2 V)) ∧ M.card = c) ∧
  ∀ M : Finset (Sym2 V), IsConnectedMatching G (M : Set (Sym2 V)) → M.card ≤ c

open Classical in
/-- A fractional coloring: nonnegative weights on independent sets, each vertex covered with weight ≥ 1. -/
def IsFractionalColoring {V : Type} [Fintype V] (G : SimpleGraph V)
    (w : {I : Finset V // G.IsIndepSet (I : Set V)} → ℝ) : Prop :=
  (∀ I, 0 ≤ w I) ∧ ∀ v : V, 1 ≤ ∑ I : {I : Finset V // G.IsIndepSet (I : Set V)} with v ∈ I.1, w I

open Classical in
/-- `x` is `χ_f(G)`: the minimum total weight of a fractional coloring. -/
def IsFractionalChromaticNumber {V : Type} [Fintype V] (G : SimpleGraph V) (x : ℝ) : Prop :=
  (∃ w, IsFractionalColoring G w ∧ ∑ I, w I = x) ∧
  ∀ w, IsFractionalColoring G w → x ≤ ∑ I, w I

/-- Theorem 1.1. -/
theorem reading_thm_1_1 :
    ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ ∃ G : SimpleGraph (Fin m),
      G.indepNum ≤ 2 ∧ ∃ c : ℕ, IsCmNumber G c ∧ (c : ℝ) < (m : ℝ) / 100 := sorry

/-- Corollary 1.2. -/
theorem reading_cor_1_2 :
    ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ 1 ≤ m ∧ ∃ G : SimpleGraph (Fin m),
      ∃ h : ℕ, IsHadwigerNumber G h ∧ ∃ x : ℝ, IsFractionalChromaticNumber G x ∧
      ∃ k : ℕ, G.chromaticNumber = k ∧
        (h : ℝ) < 26 * (m : ℝ) / 75 + 2 / 3 ∧ 26 * (m : ℝ) / 75 + 2 / 3 < (m : ℝ) / 2 ∧
        (m : ℝ) / 2 ≤ x ∧ x ≤ (k : ℝ) := sorry

/-- Hadwiger's conjecture is false. -/
theorem reading_hadwiger_false :
    ¬ ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) (h : ℕ),
      IsHadwigerNumber G h → G.chromaticNumber ≤ (h : ℕ∞) := sorry

/-
Ambiguities / choices
- h(G): defined by branch sets B : Fin t → Set V (nonempty, connected induced subgraph, pairwise disjoint,
  pairwise joined by an edge); `IsHadwigerNumber G h` says h is attained and is an upper bound, so no
  sSup/sInf/findGreatest; the number exists for finite G since t ≤ |V|. t = 0 is allowed (trivial minor).
- cm(G): "matching whose edges are pairwise touching": edges of G (Sym2), distinct edges have disjoint endpoint
  sets and some edge of G joins them. Max size by `IsCmNumber` (attained + upper bound); M finset so
  cardinality is ℕ; empty M qualifies, so cm exists. A single edge is trivially connected.
- χ_f(G): weights on independent Finsets (subtype), nonneg, coverage ≥ 1; `IsFractionalChromaticNumber`
  says minimum attained and a lower bound for all feasible. Note the empty set is independent (harmless).
  The minimum exists for finite G (LP), so the ∃ x in the theorems is not vacuous junk.
- χ(G): Mathlib `chromaticNumber : ℕ∞`; for Fin m it is finite, so I state `∃ k : ℕ, chromaticNumber = k`
  instead of toNat (no ⊤ junk). In the third theorem the comparison is in ℕ∞ with (h : ℕ∞) cast.
- α(G): Mathlib `indepNum` (ℕ, defined as sSup but bounded for finite types; used as in Mathlib).
- Ratios are in ℝ with literal fractions: cm < m/100, h < 26m/75 + 2/3 < m/2 ≤ χ_f ≤ χ.
- "Arbitrarily large m": ∀ N ∃ m ≥ N; graphs on Fin m (m vertices, finite simple). Corollary adds 1 ≤ m
  (nonempty). Corollary's order m is the vertex count.
- Third theorem quantifies over V : Type (universe 0), finite nonempty; negation of the conjecture h ≥ χ.
-/

end ReaderB

open Classical

namespace ReaderC

/-! Definitions written from the source text (abstract and Section 1). -/

/-- `t` disjoint, nonempty, pairwise-adjacent connected branch sets: a `K_t` minor model. -/
def IsCliqueMinorModel {V : Type} (G : SimpleGraph V) (t : ℕ) (B : Fin t → Set V) : Prop :=
  (∀ i, (B i).Nonempty) ∧
  (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
  (∀ i, (G.induce (B i)).Connected) ∧
  (∀ i j, i ≠ j → ∃ u ∈ B i, ∃ v ∈ B j, G.Adj u v)

/-- Hadwiger number h(G): largest t with a K_t minor. The set of such t is bounded by
the vertex count (branch sets are disjoint and nonempty) and contains 0, so `sSup` is the max. -/
noncomputable def hadwiger {V : Type} (G : SimpleGraph V) : ℕ :=
  sSup {t : ℕ | ∃ B : Fin t → Set V, IsCliqueMinorModel G t B}

/-- A connected matching: a matching (pairwise vertex-disjoint edges of G) whose edges are
pairwise touching, i.e. some edge of G joins their endpoint sets. -/
def IsConnectedMatching {V : Type} (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ x, x ∈ e → x ∉ f) ∧
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∃ u, u ∈ e ∧ ∃ v, v ∈ f ∧ G.Adj u v)

/-- cm(G): maximum size of a connected matching (the set contains 0, bounded by #edges). -/
noncomputable def cm {V : Type} (G : SimpleGraph V) : ℕ :=
  sSup {k : ℕ | ∃ M : Finset (Sym2 V), M.card = k ∧ IsConnectedMatching G M}

/-- Fractional chromatic number χ_f(G): infimum of total weight over nonnegative weightings
of independent vertex sets such that every vertex is covered with weight at least 1.
Weights are functions on all finsets; only independent ones enter the constraints and the
total. Requires `Fintype V` so that the sums are finite. -/
noncomputable def fracChromatic {V : Type} [Fintype V] (G : SimpleGraph V) : ℝ :=
  sInf {s : ℝ | ∃ w : Finset V → ℝ, (∀ I, 0 ≤ w I) ∧
    (∀ v : V, 1 ≤ ∑ I ∈ Finset.univ.filter
        (fun I : Finset V => G.IsIndepSet (I : Set V) ∧ v ∈ I), w I) ∧
    s = ∑ I ∈ Finset.univ.filter (fun I : Finset V => G.IsIndepSet (I : Set V)), w I}

/-! Readings of the claims. -/

/-- Theorem 1.1: arbitrarily large m with an m-vertex finite simple graph, α(G) ≤ 2,
cm(G) < m/100. `m` ranges over positive naturals with `N ≤ m`; `Fin m` is the vertex type. -/
theorem reading_thm_1_1 :
    ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ 0 < m ∧ ∃ G : SimpleGraph (Fin m),
      G.indepNum ≤ 2 ∧ (cm G : ℝ) < (m : ℝ) / 100 := sorry

/-- Corollary 1.2: arbitrarily large order m with
h(G) < 26m/75 + 2/3 < m/2 ≤ χ_f(G) ≤ χ(G).
χ(G) is `ℕ∞`-valued; the last inequality is stated as: χ(G) equals some natural k and
χ_f(G) ≤ k. -/
theorem reading_cor_1_2 :
    ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ 0 < m ∧ ∃ G : SimpleGraph (Fin m),
      (hadwiger G : ℝ) < 26 * (m : ℝ) / 75 + 2 / 3 ∧
      26 * (m : ℝ) / 75 + 2 / 3 < (m : ℝ) / 2 ∧
      (m : ℝ) / 2 ≤ fracChromatic G ∧
      ∃ k : ℕ, G.chromaticNumber = (k : ℕ∞) ∧ fracChromatic G ≤ (k : ℝ) := sorry

/-- Hadwiger's conjecture is false: not every finite nonempty simple graph has h(G) ≥ χ(G). -/
theorem reading_hadwiger_false :
    ¬ ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V),
      G.chromaticNumber ≤ (hadwiger G : ℕ∞) := sorry

end ReaderC

/-
AMBIGUITIES AND CHOICES (reader C, family O41 hadwiger)

1. Hadwiger number: the text says h(G) is the largest t with a K_t minor. I model a K_t minor
   as t nonempty, pairwise disjoint, connected branch sets (connectivity via G.induce) with an
   edge between every pair. Branch sets are Set V. The set of t is bounded by |V| and contains 0,
   so sSup is the true maximum for finite V. Lean's natural-number sSup on an empty/unbounded set
   would be junk, but neither occurs here.
2. Connected matching: edges are Sym2 V in a Finset, each an edge of G; matching means no vertex
   lies in two distinct edges; "touching" means some edge of G joins a vertex of one edge to a
   vertex of the other. cm(G) = sSup over sizes. Empty matching gives 0, so the set is nonempty.
3. Independence number: used Mathlib's G.indepNum (sSup over independent sets). For Fin m with m > 0
   this is the usual maximum; the bound is G.indepNum ≤ 2.
4. Arbitrarily large m: stated as for every N there is m with N ≤ m and 0 < m (nonempty), the vertex
   type being Fin m. I added 0 < m to respect "finite nonempty".
5. Fractional chromatic number: defined as an sInf over nonnegative weight functions on all finsets
   of V, with covering constraints and total weight restricted to independent sets (the text's
   I(G)). Needs Fintype V and classical decidability (open Classical). Nonempty since unit weights
   on singletons are feasible, so the sInf is not junk for nonempty V.
6. Corollary 1.2 chromatic part: χ(G) is ℕ∞-valued in Mathlib. The chain χ_f(G) ≤ χ(G) is encoded as
   "χ(G) = k for some natural k, and χ_f(G) ≤ k"; this excludes χ = ⊤, which is harmless since the
   corollary asserts finiteness via the construction. The inequality h(G) < 26m/75 + 2/3 < m/2 is
   stated in ℝ with h cast from ℕ.
7. Hadwiger's conjecture: quantified over all types V with Fintype and Nonempty (so finite nonempty
   simple graphs up to the choice of vertex type); chromatic number is Mathlib's G.chromaticNumber,
   compared to h cast to ℕ∞. Theorem 3 is the negation of the conjecture.
8. Not formalized: the fractional weakening χ_f ≤ h is only mentioned in the text, not requested
   as a separate theorem, so it is omitted (its failure follows from the corollary).
-/
