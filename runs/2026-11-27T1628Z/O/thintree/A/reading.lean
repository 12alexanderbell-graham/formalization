import Mathlib

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
