import Mathlib

open Classical

/-- `G` is `K_r`-free: no `r` vertices are pairwise adjacent (exclusion as an ordinary
subgraph, i.e. no `r`-element vertex set spans a clique). -/
def KrFree {V : Type} (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ s : Finset V, s.card = r → ¬ G.IsClique (s : Set V)

/-- `I` is an independent set: its vertices are pairwise nonadjacent. -/
def IndepSet {V : Type} (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ G.Adj u v

/-- `α(G)`: the largest size of an independent set (max of `card` over independent sets;
the family of independent sets always contains `∅`, so the `sup` is not junk). -/
noncomputable def alpha {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  ((Finset.univ : Finset V).powerset.filter (fun I => IndepSet G I)).sup Finset.card

/-- Average degree `d(G) = 2|E(G)| / n`. Only used when `n > 0` (the theorem assumes it). -/
noncomputable def avgDeg {V : Type} [Fintype V] (G : SimpleGraph V) : ℝ :=
  2 * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)

/-- Theorem 1.1: for every `r ≥ 4` there is `c_r > 0` such that every finite simple
`K_r`-free graph with `n > 0` vertices and average degree `d ≥ 2` has
`α(G) ≥ c_r · n · log d / d`. The constant `c` is chosen before the graph `V, G`. -/
theorem reading :
    ∀ r : ℕ, 4 ≤ r → ∃ c : ℝ, 0 < c ∧
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
        0 < Fintype.card V → KrFree G r → 2 ≤ avgDeg G →
        c * (Fintype.card V : ℝ) * Real.log (avgDeg G) / avgDeg G ≤ (alpha G : ℝ) := sorry

/-
AMBIGUITY NOTES (cliquefree, C reader)

1. Graphs: `SimpleGraph V` on a `Type` with `[Fintype V]`. "Finite simple graph" is encoded by
   the Fintype instance and SimpleGraph's irreflexive symmetric adjacency. Quantifying over
   `V : Type` (not arbitrary universes) is my choice.
2. `K_r`-free: read as "no r-element vertex set spans a clique", per the source's "exclusion
   means exclusion as an ordinary subgraph". Mathlib's `CliqueFree` would be equivalent; I
   wrote it out instead.
3. `α(G)`: defined as `sup` of `card` over the filtered powerset of `Finset.univ`. Since `∅`
   is independent the sup is the genuine maximum, so no `sSup`/`sInf` junk. Decidability of the
   filter comes from `open Classical`; it does not affect the statement.
4. Average degree: `2|E|/n` with `|E| = G.edgeFinset.card` and `n = Fintype.card V`. Real
   division. The hypothesis `0 < Fintype.card V` implements "n > 0" explicitly, so the `2|E|/0`
   Lean convention never enters. Without it the hypothesis `2 ≤ avgDeg G` would be false anyway.
5. `d ≥ 2` is the hypothesis `2 ≤ avgDeg G`, so `Real.log (avgDeg G)` is applied to a positive
   value (no log-of-nonpositive junk) and the division by `avgDeg G` is by a positive value.
6. `log` is `Real.log` (natural), as the source states "All logarithms are natural".
7. Quantifier order: `r` then the constant `c` (depends only on `r`), then the graph
   `V, G`. The source says "a constant c_r > 0" and "uniform in n and d", so this is the
   reading I took; the alternative (c depending on the graph) is rejected by "uniform".
8. `r ≥ 4` is the hypothesis `4 ≤ r` on the outer universal.
9. `Real.log` on `avgDeg G` in a hypothesis-guarded position is fine; no further junk.
-/
