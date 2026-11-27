import Mathlib

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
