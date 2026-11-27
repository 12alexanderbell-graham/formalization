import Mathlib

/-! # Target O, family thintree: the three blind readings of run 2026-11-27T1628Z (brief 5b216ff), concatenated unchanged
apart from the repeated `import Mathlib` lines, so a closure can import them as one module. -/


/-!
Blind reading A of O63, "The strong thin tree conjecture": Theorem 1.1.
-/

namespace ReaderA

/-- A finite loopless undirected multigraph `G = (V, E)`: finite vertex type `V`, finite edge
type `E` (parallel edges are distinct elements of `E`), and an endpoint map `ends : E → Sym2 V`
with no loops. -/
structure Multigraph (V E : Type) [Fintype V] [Fintype E] where
  ends : E → Sym2 V
  loopless : ∀ e, ¬ (ends e).IsDiag

variable {V E : Type} [Fintype V] [Fintype E]

/-- Edge `e` has exactly one endpoint in `S`. -/
def Crosses (G : Multigraph V E) (S : Set V) (e : E) : Prop :=
  ∃ u ∈ S, ∃ w ∉ S, G.ends e = s(u, w)

/-- `δ_F(S)` for a set of edges `F ⊆ E`: edges of `F` with exactly one endpoint in `S`.
`δ_G(S) = cut G Set.univ S`, `δ_T(S) = cut G T S`. -/
def cut (G : Multigraph V E) (F : Set E) (S : Set V) : Set E :=
  {e | e ∈ F ∧ Crosses G S e}

/-- A nonempty proper subset `S` of `V`. -/
def NonemptyProper (S : Set V) : Prop := S.Nonempty ∧ S ≠ Set.univ

/-- `G` is `k`-edge-connected: `|δ_G(S)| ≥ k` for every nonempty proper `S`.
Cardinalities are `Set.ncard` of finite sets (all sets of edges are finite). -/
def KEdgeConnected (G : Multigraph V E) (k : ℕ) : Prop :=
  ∀ S : Set V, NonemptyProper S → k ≤ (cut G Set.univ S).ncard

/-- `T ⊆ E` is a spanning tree of `G`: no two edges of `T` are parallel, and the simple graph on
all of `V` with edge set `{ends e : e ∈ T}` is a tree (connected and acyclic). -/
def IsSpanningTree (G : Multigraph V E) (T : Set E) : Prop :=
  Set.InjOn G.ends T ∧ (SimpleGraph.fromEdgeSet (G.ends '' T)).IsTree

/-- Theorem 1.1 (strong thin tree theorem). -/
theorem reading_thm_1_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ), 1 ≤ k →
      ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E),
        2 ≤ Fintype.card V → KEdgeConnected G k →
        ∃ T : Set E, IsSpanningTree G T ∧
          ∀ S : Set V, NonemptyProper S →
            ((cut G T S).ncard : ℝ) ≤ C / k * ((cut G Set.univ S).ncard : ℝ) := sorry

end ReaderA

/-
AMBIGUITIES AND CHOICES

1. Multigraph: finite vertex type `V`, finite edge type `E`, endpoint map `E → Sym2 V`
   (undirected), parallel edges = distinct edges with the same `Sym2` value ("counted
   separately"). Loopless: `ends e` is never a diagonal `s(v,v)`. `V`, `E` live in `Type`
   (finite, so no loss of generality).

2. δ_G(S): edges with exactly one endpoint in S, written as `∃ u ∈ S, ∃ w ∉ S, ends e = s(u,w)`.
   Sizes `|·|` are `Set.ncard` (sets are finite, so not the junk value 0 for infinite sets).

3. "nonempty proper subset S ⊂ V": `S.Nonempty ∧ S ≠ univ`.

4. k-edge-connected: `k ≤ |δ_G(S)|` for all nonempty proper S, exactly as the text defines it.
   `k : ℕ` with `1 ≤ k`, so `C / k` divides by a positive real (no x/0 junk).

5. Spanning tree: a set of edges T ⊆ E such that the subgraph (V, T) is a tree. Since a tree has
   no cycles, it has no two parallel edges; I encode this as `Set.InjOn ends T` plus
   `IsTree` of the simple graph on V with edge set `ends '' T` (Mathlib `SimpleGraph.IsTree` =
   connected (hence V nonempty) and acyclic). Spanning = vertex set all of V, built in since
   the simple graph lives on all of V. Without the injectivity clause, a "tree" could carry
   duplicate parallel copies, which would be a 2-cycle in the multigraph; so the clause is
   required. δ_T(S) is the edges of T crossing S.

6. "universal constant C > 0": `∃ C : ℝ, 0 < C`, chosen before k and G. The inequality is in ℝ:
   `|δ_T(S)| ≤ (C/k) |δ_G(S)|`.

7. "at least two vertices": `2 ≤ Fintype.card V`.
-/


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


/-!
Blind reading C, target O, family O63: The strong thin tree conjecture.
Definitions are written from the source excerpt; the claim is `sorry`.
See the comment block at the end for ambiguities and choices.
-/

namespace ReaderC

/-- For a multigraph with endpoint map `ends : E → Sym2 V` (parallel edges are distinct
elements of E with equal endpoints), an edge e crosses the cut of S iff exactly one of its
endpoints lies in S. For loopless edges this is the same as "one endpoint in S, one outside". -/
def Crosses {V E : Type} (ends : E → Sym2 V) (S : Finset V) (e : E) : Prop :=
  (∃ v ∈ ends e, v ∈ S) ∧ (∃ w ∈ ends e, w ∉ S)

/-- |δ_F(S)|: the number of edges of F ⊆ E crossing the cut of S. -/
noncomputable def cutSize {V E : Type} [Fintype E] (ends : E → Sym2 V) (S : Finset V)
    (F : Set E) : ℕ :=
  Set.ncard {e : E | e ∈ F ∧ Crosses ends S e}

/-- k-edge-connected: |δ_G(S)| ≥ k for every nonempty proper S ⊂ V. -/
def KEdgeConnected {V E : Type} [Fintype V] [Fintype E] (ends : E → Sym2 V) (k : ℕ) : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → k ≤ cutSize ends S Set.univ

/-- T ⊆ E is a spanning tree of the loopless multigraph (V, ends): the simple graph on V whose
edges are the endpoint pairs of T is connected, and |T| = |V| − 1. -/
def IsSpanningTree {V E : Type} [Fintype V] [Fintype E] (ends : E → Sym2 V) (T : Set E) : Prop :=
  (SimpleGraph.fromEdgeSet ((fun e => ends e) '' T)).Connected ∧
    T.ncard + 1 = Fintype.card V

/-- Theorem 1.1: a universal constant C > 0 such that every finite loopless k-edge-connected
multigraph (k ≥ 1, at least two vertices) has a spanning tree T with
|δ_T(S)| ≤ (C/k)|δ_G(S)| for every nonempty proper S ⊂ V. -/
theorem reading_thm_1_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V E : Type) [Fintype V] [Fintype E] (ends : E → Sym2 V),
        (∀ e : E, ¬ (ends e).IsDiag) →
        ∀ k : ℕ, 1 ≤ k → 2 ≤ Fintype.card V →
          KEdgeConnected ends k →
          ∃ T : Set E, IsSpanningTree ends T ∧
            ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
              (cutSize ends S T : ℝ) ≤ (C / (k : ℝ)) * (cutSize ends S Set.univ : ℝ) :=
  sorry

end ReaderC

/-!
## Comment block: ambiguities and choices (reader C, O63)

1. Multigraphs. A finite loopless multigraph is given as a finite vertex type V, a finite edge
   type E, and an endpoint map `ends : E → Sym2 V`. Parallel edges are distinct elements of E with
   the same endpoint pair, which is what "parallel edges are counted separately" requires. Loopless
   means ¬ (ends e).IsDiag for every e. The theorem carries this hypothesis explicitly.
   Mathlib has no finite multigraph API suited to this, so this encoding is the one I wrote.

2. Cuts. δ_G(S) is the set of edges with exactly one endpoint in S. `Crosses` says "some endpoint in
   S and some endpoint not in S". For loopless edges (two distinct endpoints) this is exactly
   "exactly one endpoint in S". Proper nonempty S ⊂ V is `S : Finset V` with `S.Nonempty` and
   `S ≠ Finset.univ`.

3. Set.ncard. `cutSize` counts with `Set.ncard`, which avoids decidability instances. E is finite, so
   ncard is the honest cardinality and cannot silently be 0 from infinitude. Edge sets are `Set E`.

4. k-edge-connectivity: "|δ_G(S)| ≥ k for every nonempty proper S" is `KEdgeConnected`, with k : ℕ.
   The theorem requires 1 ≤ k, so no division by zero occurs in C/k (k is cast to ℝ and is ≥ 1).

5. Spanning trees. The text says "a spanning tree retains connectivity using |V|−1 edges" and the
   notion is for the multigraph. I define a spanning tree T ⊆ E as: the simple graph on V whose edges
   are the endpoint pairs of T (via `SimpleGraph.fromEdgeSet`, which drops loops; none occur) is
   connected, and |T| = |V| − 1. A connected multigraph on n vertices with n − 1 edges is a tree
   (no cycles, no parallel edges), so this is the correct definition of a spanning tree of the
   multigraph. Note that `fromEdgeSet` identifies parallel copies, which is why the count |T| is
   separate from the connectivity clause.

6. Thinness. α-thin with α = C/k: for every nonempty proper S, |δ_T(S)| ≤ (C/k)|δ_G(S)|, where
   δ_T(S) = edges of T crossing S (`cutSize ends S T`). The inequality is over ℝ with k cast.

7. The constant. "There is a universal constant C>0" is `∃ C : ℝ, 0 < C ∧ ...`. The quantifier over
   V, E, and the endpoint maps is inside the ∃ C, as "universal" requires. V and E are in `Type`
   (universe 0) since the text concerns finite multigraphs.

8. Junk values. `Set.ncard` returns 0 for infinite sets; not an issue since E and V are Fintype.
   The condition "at least two vertices" is `2 ≤ Fintype.card V`. For S nonempty and proper,
   the cut counts are integers and the real inequality is faithful. No division by a zero value
   occurs, since k ≥ 1.

9. Not formalised: the introduction's remarks on the question (no hidden hypotheses there) and the
   omitted lines. The abstract and Theorem 1.1 are both covered by `reading_thm_1_1`.
-/
