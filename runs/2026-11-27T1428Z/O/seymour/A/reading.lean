import Mathlib

namespace ReaderA

/-- "An oriented graph is a finite directed graph with no loops, no multiple arcs, and no pair of
opposite arcs."  A Mathlib `Digraph` is an arc relation, so it has no multiple arcs by
construction; finiteness is carried by `[Fintype V]` in the statements. -/
def IsOriented {V : Type} (G : Digraph V) : Prop :=
  (∀ v, ¬ G.Adj v v) ∧ (∀ u v, G.Adj u v → ¬ G.Adj v u)

/-- `N₁⁺(v) = {u : v → u}`. -/
def N1 {V : Type} (G : Digraph V) (v : V) : Set V :=
  {u | G.Adj v u}

/-- `N₂⁺(v) = {w ∉ {v} ∪ N₁⁺(v) : there is a vertex u with v → u → w}`. -/
def N2 {V : Type} (G : Digraph V) (v : V) : Set V :=
  {w | w ∉ ({v} ∪ N1 G v) ∧ ∃ u, G.Adj v u ∧ G.Adj u w}

/-- Theorem 1.1: every nonempty finite oriented graph has a vertex `v` with
`|N₁⁺(v)| ≤ |N₂⁺(v)|`. -/
theorem reading_thm_1_1 (V : Type) [Fintype V] [Nonempty V] (G : Digraph V)
    (hG : IsOriented G) :
    ∃ v : V, (N1 G v).ncard ≤ (N2 G v).ncard := sorry

/-- A directed triangle: arcs `a → b → c → a`.  (In an oriented graph `a, b, c` are then
automatically pairwise distinct: no loops and no opposite arcs.) -/
def HasDirectedTriangle {V : Type} (G : Digraph V) : Prop :=
  ∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a

/-- Directed-triangle consequence -- NOT READ FROM THE EXCERPT (see comment block below):
every nonempty finite oriented graph in which every vertex has out-degree at least one third of
its order (`3 · |N₁⁺(v)| ≥ |V|`) contains a directed triangle. -/
theorem reading_triangle (V : Type) [Fintype V] [Nonempty V] (G : Digraph V)
    (hG : IsOriented G) (hdeg : ∀ v : V, Fintype.card V ≤ 3 * (N1 G v).ncard) :
    HasDirectedTriangle G := sorry

end ReaderA

/-
Reader A -- ambiguities and choices

1. The excerpt.  The file given (abstract + introduction lines 1-35) ends mid-sentence:
   "Section~\ref{sec:directed-cycle-consequences} records consequences for".  It contains NO
   directed-triangle statement and the phrase "at least one third of its order" does not occur
   in it.  So `reading_triangle` is not a reading of the source; it is my guess at the
   standard consequence the brief alludes to (the triangle case of Caccetta-Haggkvist with
   minimum out-degree at least n/3).  It should be compared with the other readers only as a
   guess, or discarded.  Its reading of "at least one third of its order": every vertex `v`
   has out-degree `|N₁⁺(v)| ≥ |V|/3`, written in ℕ as `|V| ≤ 3 * |N₁⁺(v)|` to avoid ℕ
   division (floor) -- it is the exact real inequality `deg ≥ n/3`.  "Order" = number of
   vertices = `Fintype.card V`.  I added `[Nonempty V]`: for the empty graph the degree
   hypothesis holds vacuously and there is no triangle.

2. "oriented graph": `Digraph V` (an arc relation, so no multiple arcs automatically) plus
   `IsOriented` = irreflexive (no loops) and asymmetric (no pair of opposite arcs).  The
   irreflexivity clause is implied by asymmetry but kept as the text lists it.  "finite" is
   `[Fintype V]`; "nonempty" is `[Nonempty V]`.  No connectivity / completeness assumption
   ("need not be complete or connected").  Vertex type is in `Type` (universe 0); the
   statement for finite graphs is universe-independent in content.

3. N₁⁺, N₂⁺ are transcribed literally as sets; in particular `N₂⁺` explicitly excludes `v` and
   `N₁⁺(v)` ("removing vertices already reached in one step is essential"), and each vertex is
   counted once because it is a set.

4. Cardinalities `|·|` are `Set.ncard`.  Junk avoided: `V` is a `Fintype`, so every subset is
   finite and `ncard` is the true cardinality (no "infinite set ↦ 0" case can arise).  The
   comparison `≤` is in ℕ; no subtraction or division appears.

5. "a vertex v such that ..." is an existential over `V`; "every nonempty finite oriented
   graph" is a universal over finite nonempty types and digraphs on them.
-/
