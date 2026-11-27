import Mathlib

/-! # Target O, family seymour: the three blind readings of run 2026-11-27T1428Z (brief 0ed6b5c), concatenated unchanged
apart from the repeated `import Mathlib` lines, so a closure can import them as one module. -/


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


namespace ReaderC

open scoped Classical

/-- An oriented graph on vertex type `V`, given by its arc relation `adj`
(`adj u v` means the arc `u → v`). Loopless, and no pair of opposite arcs.
Multiple arcs are impossible because `adj` is a proposition, not a multiset. -/
def IsOrientedGraph {V : Type} (adj : V → V → Prop) : Prop :=
  (∀ v : V, ¬ adj v v) ∧ (∀ u v : V, adj u v → ¬ adj v u)

/-- `N₁⁺(v) = {u : v → u}`. -/
noncomputable def outN1 {V : Type} [Fintype V] (adj : V → V → Prop) (v : V) : Finset V :=
  Finset.univ.filter (fun u => adj v u)

/-- `N₂⁺(v)`: vertices `w ∉ {v} ∪ N₁⁺(v)` with some `u` such that `v → u → w`. -/
noncomputable def outN2 {V : Type} [Fintype V] (adj : V → V → Prop) (v : V) : Finset V :=
  Finset.univ.filter (fun w => w ≠ v ∧ ¬ adj v w ∧ ∃ u : V, adj v u ∧ adj u w)

/-- Theorem 1.1 (Seymour's second neighborhood conjecture, positive resolution). -/
theorem reading_seymour_thm1_1 :
    ∀ (V : Type) [Fintype V] [Nonempty V] (adj : V → V → Prop),
      IsOrientedGraph adj → ∃ v : V, (outN1 adj v).card ≤ (outN2 adj v).card := by
  sorry

/-!
## Ambiguities and choices (reader C, O44)

1. Vertex type. "Finite oriented graph" is read as a finite `Fintype V` with `Nonempty V`
   (nonempty), plus an arc relation `adj : V → V → Prop`. Loops are excluded by
   `∀ v, ¬ adj v v`; opposite arcs by `∀ u v, adj u v → ¬ adj v u`. No multiple arcs is
   automatic for a relation. The underlying graph need not be connected or complete
   (no hypothesis added), as the excerpt says.

2. `N₁⁺`, `N₂⁺` are `Finset`s (via `Finset.univ.filter`), so the cardinalities are
   honest natural numbers over a finite type; no `Set.ncard` junk value can arise.
   Classical decidability is used for the filters (`open scoped Classical`).

3. `N₂⁺(v)`: I took the text literally: `w ≠ v`, `¬ adj v w` (i.e. `w ∉ N₁⁺(v)`), and
   `∃ u, adj v u ∧ adj u w`. The text's "there is a vertex u with v → u → w" is read with
   `u` any vertex (it may be in `N₁⁺(v)`, which it always is when `v → u`).
   Each vertex is counted once (it is a Finset).

4. Theorem statement: `∃ v, |N₁⁺(v)| ≤ |N₂⁺(v)|` with `|·|` the Finset card (a natural
   number). Real-valued or `ℕ∞` values are not needed.

5. The second theorem (directed-triangle consequence, "at least one third of its order")
   is NOT written. The excerpt I was given (lines 1-35 of the introduction, as the brief
   names them) does not contain that sentence: lines 34-35 only mention Seacrest's
   weighted equivalences, and the section pointer at lines 40-41 is cut off before any
   triangle statement. The brief forbids opening any other file, so I could not formalize
   it. The file therefore has only Theorem 1.1. Note also that the named file, as opened,
   has 41 lines rather than 35; I used only the content shown in lines 1-35 plus the
   truncated pointer on lines 36-41, and I did not look further.

6. Not written: the weighted forms (Seacrest's equivalences); they are outside the
   brief's list for this family.
-/

end ReaderC
