import Mathlib

namespace ReaderB

/-- An oriented graph on a finite vertex type: no loops, no multiple arcs (a `Prop`-valued relation),
no pair of opposite arcs.  (Asymmetry already implies irreflexivity; both are stated for fidelity.) -/
structure OrientedGraph (V : Type) [Fintype V] where
  adj : V → V → Prop
  loopless : ∀ v, ¬ adj v v
  no_opposite : ∀ u v, adj u v → ¬ adj v u

namespace OrientedGraph
variable {V : Type} [Fintype V] (G : OrientedGraph V)

/-- `N₁⁺(v) = {u : v → u}` -/
def N1 (v : V) : Set V := {u | G.adj v u}

/-- `N₂⁺(v) = {w ∉ {v} ∪ N₁⁺(v) : ∃ u, v → u → w}` -/
def N2 (v : V) : Set V := {w | w ∉ ({v} ∪ G.N1 v) ∧ ∃ u, G.adj v u ∧ G.adj u w}

end OrientedGraph

/-- Theorem 1.1. -/
theorem reading_seymour_second_neighborhood (V : Type) [Fintype V] [Nonempty V]
    (G : OrientedGraph V) : ∃ v : V, (G.N1 v).ncard ≤ (G.N2 v).ncard := sorry

/-- Directed-triangle consequence (Caccetta–Häggkvist for r = 3): a nonempty finite oriented graph
in which every vertex has out-degree at least one third of the order contains a directed triangle. -/
theorem reading_seymour_directed_triangle (V : Type) [Fintype V] [Nonempty V]
    (G : OrientedGraph V) (h : ∀ v, Fintype.card V ≤ 3 * (G.N1 v).ncard) :
    ∃ a b c : V, G.adj a b ∧ G.adj b c ∧ G.adj c a := sorry

end ReaderB

/-
Ambiguities and choices.
* Vertex set: a `Fintype` type `V`; nonemptiness is the instance `[Nonempty V]`.  Oriented graph =
  structure with a relation `adj` (no multiple arcs automatically), loopless, no opposite pair.
* N₁, N₂ transcribed literally as sets; `N₂` excludes `{v} ∪ N₁⁺(v)`.  Cardinalities use `Set.ncard`;
  safe since `V` is finite, so all sets are finite (no infinite-set junk).  No ℕ subtraction, no division.
* IMPORTANT: the excerpt I was given (lines 1-35 of the file, which in fact ends mid-sentence at
  "Section ... records consequences for") does NOT contain the directed-triangle sentence, so the second
  theorem is my reconstruction, not a literal reading: the standard consequence of the second
  neighbourhood conjecture, the r = 3 case of Caccetta-Haggkvist.  I read "at least one third of its order"
  as: every vertex has out-degree d⁺(v) with 3·d⁺(v) ≥ |V| (stated without division, in ℕ), and the
  conclusion as the existence of a directed 3-cycle a→b→c→a (a,b,c are then automatically distinct since
  the graph is loopless and has no opposite arcs).  Nonemptiness is needed (the empty graph has no triangle).
  Out-degree is `(G.N1 v).ncard`.
-/
