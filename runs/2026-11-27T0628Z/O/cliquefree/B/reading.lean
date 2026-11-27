import Mathlib

open Classical

/-- Number of edges of a finite simple graph. -/
noncomputable def edgeCount {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Nat.card G.edgeSet

/-- Average degree d(G) = 2|E(G)| / n, as a real number. -/
noncomputable def avgDegree {V : Type} [Fintype V] (G : SimpleGraph V) : ℝ :=
  2 * (edgeCount G : ℝ) / (Fintype.card V : ℝ)

/-- `G` has an independent set of at least `k` vertices (so α(G) ≥ k). -/
def HasIndepSetOfSize {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℝ) : Prop :=
  ∃ s : Finset V, G.IsIndepSet (s : Set V) ∧ k ≤ (s.card : ℝ)

theorem reading :
    ∀ r : ℕ, 4 ≤ r →
      ∃ c : ℝ, 0 < c ∧
        ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
          0 < Fintype.card V →
          G.CliqueFree r →
          2 ≤ avgDegree G →
          HasIndepSetOfSize G
            (c * (Fintype.card V : ℝ) * Real.log (avgDegree G) / avgDegree G) := sorry

/-
Ambiguities and choices.
* Graph: finite simple graph = `SimpleGraph V` with `[Fintype V]`, V : Type (universe 0; harmless
  since the statement is invariant under relabelling and every finite graph has a Type-0 copy).
* n = Fintype.card V, with explicit hypothesis 0 < n (source: "n > 0 vertices").
* Edge count: `Nat.card G.edgeSet` (finite, so no junk 0 from infiniteness).
* Average degree: real 2|E|/n; n > 0 so no division by zero. d ≥ 2 > 0, so `Real.log d` is the
  genuine natural log of a positive number (>= log 2 > 0) and dividing by d is safe.
* α(G) ≥ x: stated as existence of an independent finset of cardinality ≥ x (real inequality),
  avoiding `indepNum`/`sSup`. Equivalent to α(G) ≥ x since α is a max over a finite nonempty family.
* K_r-free: `G.CliqueFree r` (no r pairwise adjacent vertices; for cliques "subgraph" vs
  "induced subgraph" coincide).
* Quantifier order: ∀ r ≥ 4, ∃ c > 0, ∀ graphs. c depends only on r. r : ℕ.
* "log" natural: Real.log.
-/
