import Mathlib

namespace ReaderB

universe u

/-- A finite loopless undirected multigraph on vertex type `V` with edge type `E`: each edge has an
unordered pair of endpoints, and the endpoints are distinct.  Parallel edges are distinct
elements of `E` with equal `ends`. -/
structure Multigraph (V E : Type u) where
  ends : E → Sym2 V
  loopless : ∀ e, ¬ (ends e).IsDiag

namespace Multigraph

variable {V E : Type u}

/-- `e` has exactly one endpoint in `S`. -/
def Crosses (G : Multigraph V E) (S : Set V) (e : E) : Prop :=
  (∃ v ∈ G.ends e, v ∈ S) ∧ (∃ w ∈ G.ends e, w ∉ S)

/-- `δ_G(S)`, as a set of edges (the edges of the subset `F ⊆ E` that cross `S`). -/
def cut (G : Multigraph V E) (F : Set E) (S : Set V) : Set E := {e | e ∈ F ∧ G.Crosses S e}

/-- `k`-edge-connected: `|δ_G(S)| ≥ k` for every nonempty proper `S`. -/
def EdgeConnected (G : Multigraph V E) (k : ℕ) : Prop :=
  ∀ S : Set V, S.Nonempty → S ≠ Set.univ → k ≤ (G.cut Set.univ S).ncard

/-- The simple graph on `V` whose edges are the underlying pairs of the edges in `F`. -/
def underlying (G : Multigraph V E) (F : Set E) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (G.ends '' F)

/-- `F` is the edge set of a spanning tree of `G`: the edges of `F` connect all vertices and
`|F| + 1 = |V|`.  (A connected multigraph with `|V| - 1` edges is a tree; no cycle, including
a 2-cycle from parallel edges, can occur.) -/
def IsSpanningTree [Fintype V] (G : Multigraph V E) (F : Set E) : Prop :=
  (G.underlying F).Connected ∧ F.ncard + 1 = Fintype.card V

end Multigraph

/-- Theorem 1.1. -/
theorem readingThinTree :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), 1 ≤ k →
      ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E),
        2 ≤ Fintype.card V → G.EdgeConnected k →
        ∃ T : Set E, G.IsSpanningTree T ∧
          ∀ S : Set V, S.Nonempty → S ≠ Set.univ →
            ((G.cut T S).ncard : ℝ) ≤ C / (k : ℝ) * ((G.cut Set.univ S).ncard : ℝ) := by
  sorry

/-
AMBIGUITIES AND CHOICES
* Multigraph: own structure, edges `E` with `ends : E → Sym2 V`; loopless means no diagonal
  pair.  Finite: `Fintype V`, `Fintype E`.  Parallel edges are separate elements of `E`.
* Universe: V and E are quantified over `Type` (universe 0), enough for finite graphs
  (any finite graph is isomorphic to one in Type).
* δ_G(S): `cut univ S`, the edges with exactly one endpoint in S; δ_T(S) = `cut T S` for T ⊆ E.
  Cardinalities via `Set.ncard`, correct since E is finite (no infinite-set junk).
* Nonempty proper S: `S.Nonempty ∧ S ≠ univ`.
* k-edge-connected: `k ≤ ncard (δ_G S)` for all nonempty proper S.  k ≥ 1 as `1 ≤ k` (ℕ), so
  the division by `(k : ℝ)` is never by 0.  No ℕ subtraction used.
* Spanning tree: a set T of edges such that the simple graph of their endpoint pairs is
  connected on V and `|T| + 1 = |V|` (avoids ℕ subtraction |V|-1).  For a multigraph this is
  equivalent to being a tree (connected + n-1 edges forces acyclic, and rules out parallel
  edge pairs since collapsing them would drop connectivity below the count).  Not using
  `SimpleGraph.IsTree` directly, because collapsing parallel edges would make it unsound.
* Constant: `∃ C : ℝ, 0 < C`, universal (before the quantification on k and G).
  Inequality in ℝ: `|δ_T S| ≤ (C/k) * |δ_G S|`.
* `2 ≤ card V` hypothesis as stated.
-/

end ReaderB
