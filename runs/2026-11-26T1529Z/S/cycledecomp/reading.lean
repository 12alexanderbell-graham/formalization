import Mathlib

open SimpleGraph

namespace CycleDecomp

variable {V : Type*}

/-- "a cycle is simple and has length at least three": `S` is the edge set of some
`SimpleGraph.Walk.IsCycle` walk in `G` (Mathlib's `IsCycle` already forces length ≥ 3). -/
def IsCycleEdgeSet (G : SimpleGraph V) (S : Set (Sym2 V)) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ {e | e ∈ p.edges} = S

/-- "each of which is the edge set of a cycle or consists of a single edge". -/
def IsCycleOrEdge (G : SimpleGraph V) (S : Set (Sym2 V)) : Prop :=
  IsCycleEdgeSet G S ∨ ∃ e ∈ G.edgeSet, S = {e}

/-- "E(G) has a partition into [k] parts, each of which is the edge set of a cycle or a single
edge": a family of `k` parts, pairwise disjoint, with union `E(G)`, each a cycle or single edge.
(Parts are automatically nonempty, so indexing by `Fin k` does not hide repeated parts.) -/
def IsCycleEdgeDecomposition (G : SimpleGraph V) {k : ℕ} (parts : Fin k → Set (Sym2 V)) : Prop :=
  (∀ i, IsCycleOrEdge G (parts i)) ∧
  (∀ i j, i ≠ j → Disjoint (parts i) (parts j)) ∧
  (⋃ i, parts i) = G.edgeSet

/-- "There is an absolute constant C>0 such that, for every finite simple undirected graph G with
n vertices, E(G) has a partition into at most Cn parts, each of which is the edge set of a cycle
or consists of a single edge." -/
theorem reading :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∃ (k : ℕ) (parts : Fin k → Set (Sym2 V)),
        IsCycleEdgeDecomposition G parts ∧ (k : ℝ) ≤ C * Fintype.card V := by
  sorry

end CycleDecomp

/-
`reading_erdos` omitted: the Erdős statement "Any graph on n vertices can be decomposed into O(n)
many edge-disjoint cycles and edges" is the same as `reading` (O(n) read as ≤ C n, n ≥ 1 or the
empty graph, where k = 0 works).

Ambiguities:
- "O(n)": read as a uniform constant C>0 with count ≤ C·n (as the manuscript states); for n = 0
  the bound forces k = 0, which is fine since there are no edges.
- Graph model: `SimpleGraph V` with `V : Type` a `Fintype`, n = `Fintype.card V` (isolated vertices
  count in n, as in the manuscript).
- Cycle: Mathlib `Walk.IsCycle` (closed, nonempty, trail, internal vertices distinct; length ≥ 3
  automatic in simple graphs). Cycle's "edge set" = set of edges of the walk.
- Partition: indexed family `Fin k → Set (Sym2 V)`, pairwise disjoint, union = edgeSet; since
  parts are nonempty, this equals a partition into k distinct parts. "At most Cn parts" = k ≤ C n.
- "Edge-disjoint cycles and edges": parts may share vertices, not edges (as the manuscript says).
- Universe: V quantified in `Type` (not `Type*`) inside the existential-constant statement so C
  does not depend on V.
-/
