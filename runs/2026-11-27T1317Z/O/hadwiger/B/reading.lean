import Mathlib

namespace ReaderB

open SimpleGraph

/-- `G` has a `K_t` minor: `t` nonempty, pairwise disjoint, connected branch sets, any two joined by an edge. -/
def HasCliqueMinor {V : Type} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ B : Fin t → Set V, (∀ i, (B i).Nonempty) ∧ (∀ i, (G.induce (B i)).Connected) ∧
    Pairwise (Function.onFun Disjoint B) ∧
    ∀ i j, i ≠ j → ∃ u ∈ B i, ∃ v ∈ B j, G.Adj u v

/-- `h` is the Hadwiger number: the largest `t` with a `K_t` minor. -/
def IsHadwigerNumber {V : Type} (G : SimpleGraph V) (h : ℕ) : Prop :=
  HasCliqueMinor G h ∧ ∀ t, HasCliqueMinor G t → t ≤ h

/-- A connected matching: a set of edges of `G`, pairwise disjoint, pairwise touching. -/
def IsConnectedMatching {V : Type} (G : SimpleGraph V) (M : Set (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint {v | v ∈ e} {v | v ∈ f}) ∧
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∃ u ∈ e, ∃ v ∈ f, G.Adj u v)

/-- `c` is `cm(G)`: the maximum cardinality of a (finite) connected matching. -/
def IsCmNumber {V : Type} (G : SimpleGraph V) (c : ℕ) : Prop :=
  (∃ M : Finset (Sym2 V), IsConnectedMatching G (M : Set (Sym2 V)) ∧ M.card = c) ∧
  ∀ M : Finset (Sym2 V), IsConnectedMatching G (M : Set (Sym2 V)) → M.card ≤ c

open Classical in
/-- A fractional coloring: nonnegative weights on independent sets, each vertex covered with weight ≥ 1. -/
def IsFractionalColoring {V : Type} [Fintype V] (G : SimpleGraph V)
    (w : {I : Finset V // G.IsIndepSet (I : Set V)} → ℝ) : Prop :=
  (∀ I, 0 ≤ w I) ∧ ∀ v : V, 1 ≤ ∑ I : {I : Finset V // G.IsIndepSet (I : Set V)} with v ∈ I.1, w I

open Classical in
/-- `x` is `χ_f(G)`: the minimum total weight of a fractional coloring. -/
def IsFractionalChromaticNumber {V : Type} [Fintype V] (G : SimpleGraph V) (x : ℝ) : Prop :=
  (∃ w, IsFractionalColoring G w ∧ ∑ I, w I = x) ∧
  ∀ w, IsFractionalColoring G w → x ≤ ∑ I, w I

/-- Theorem 1.1. -/
theorem reading_thm_1_1 :
    ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ ∃ G : SimpleGraph (Fin m),
      G.indepNum ≤ 2 ∧ ∃ c : ℕ, IsCmNumber G c ∧ (c : ℝ) < (m : ℝ) / 100 := sorry

/-- Corollary 1.2. -/
theorem reading_cor_1_2 :
    ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ 1 ≤ m ∧ ∃ G : SimpleGraph (Fin m),
      ∃ h : ℕ, IsHadwigerNumber G h ∧ ∃ x : ℝ, IsFractionalChromaticNumber G x ∧
      ∃ k : ℕ, G.chromaticNumber = k ∧
        (h : ℝ) < 26 * (m : ℝ) / 75 + 2 / 3 ∧ 26 * (m : ℝ) / 75 + 2 / 3 < (m : ℝ) / 2 ∧
        (m : ℝ) / 2 ≤ x ∧ x ≤ (k : ℝ) := sorry

/-- Hadwiger's conjecture is false. -/
theorem reading_hadwiger_false :
    ¬ ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) (h : ℕ),
      IsHadwigerNumber G h → G.chromaticNumber ≤ (h : ℕ∞) := sorry

/-
Ambiguities / choices
- h(G): defined by branch sets B : Fin t → Set V (nonempty, connected induced subgraph, pairwise disjoint,
  pairwise joined by an edge); `IsHadwigerNumber G h` says h is attained and is an upper bound, so no
  sSup/sInf/findGreatest; the number exists for finite G since t ≤ |V|. t = 0 is allowed (trivial minor).
- cm(G): "matching whose edges are pairwise touching": edges of G (Sym2), distinct edges have disjoint endpoint
  sets and some edge of G joins them. Max size by `IsCmNumber` (attained + upper bound); M finset so
  cardinality is ℕ; empty M qualifies, so cm exists. A single edge is trivially connected.
- χ_f(G): weights on independent Finsets (subtype), nonneg, coverage ≥ 1; `IsFractionalChromaticNumber`
  says minimum attained and a lower bound for all feasible. Note the empty set is independent (harmless).
  The minimum exists for finite G (LP), so the ∃ x in the theorems is not vacuous junk.
- χ(G): Mathlib `chromaticNumber : ℕ∞`; for Fin m it is finite, so I state `∃ k : ℕ, chromaticNumber = k`
  instead of toNat (no ⊤ junk). In the third theorem the comparison is in ℕ∞ with (h : ℕ∞) cast.
- α(G): Mathlib `indepNum` (ℕ, defined as sSup but bounded for finite types; used as in Mathlib).
- Ratios are in ℝ with literal fractions: cm < m/100, h < 26m/75 + 2/3 < m/2 ≤ χ_f ≤ χ.
- "Arbitrarily large m": ∀ N ∃ m ≥ N; graphs on Fin m (m vertices, finite simple). Corollary adds 1 ≤ m
  (nonempty). Corollary's order m is the vertex count.
- Third theorem quantifies over V : Type (universe 0), finite nonempty; negation of the conjecture h ≥ χ.
-/

end ReaderB
