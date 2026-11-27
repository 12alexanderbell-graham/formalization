import Mathlib

open Classical

namespace ReaderC

/-! Definitions written from the source text (abstract and Section 1). -/

/-- `t` disjoint, nonempty, pairwise-adjacent connected branch sets: a `K_t` minor model. -/
def IsCliqueMinorModel {V : Type} (G : SimpleGraph V) (t : ℕ) (B : Fin t → Set V) : Prop :=
  (∀ i, (B i).Nonempty) ∧
  (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
  (∀ i, (G.induce (B i)).Connected) ∧
  (∀ i j, i ≠ j → ∃ u ∈ B i, ∃ v ∈ B j, G.Adj u v)

/-- Hadwiger number h(G): largest t with a K_t minor. The set of such t is bounded by
the vertex count (branch sets are disjoint and nonempty) and contains 0, so `sSup` is the max. -/
noncomputable def hadwiger {V : Type} (G : SimpleGraph V) : ℕ :=
  sSup {t : ℕ | ∃ B : Fin t → Set V, IsCliqueMinorModel G t B}

/-- A connected matching: a matching (pairwise vertex-disjoint edges of G) whose edges are
pairwise touching, i.e. some edge of G joins their endpoint sets. -/
def IsConnectedMatching {V : Type} (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ x, x ∈ e → x ∉ f) ∧
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∃ u, u ∈ e ∧ ∃ v, v ∈ f ∧ G.Adj u v)

/-- cm(G): maximum size of a connected matching (the set contains 0, bounded by #edges). -/
noncomputable def cm {V : Type} (G : SimpleGraph V) : ℕ :=
  sSup {k : ℕ | ∃ M : Finset (Sym2 V), M.card = k ∧ IsConnectedMatching G M}

/-- Fractional chromatic number χ_f(G): infimum of total weight over nonnegative weightings
of independent vertex sets such that every vertex is covered with weight at least 1.
Weights are functions on all finsets; only independent ones enter the constraints and the
total. Requires `Fintype V` so that the sums are finite. -/
noncomputable def fracChromatic {V : Type} [Fintype V] (G : SimpleGraph V) : ℝ :=
  sInf {s : ℝ | ∃ w : Finset V → ℝ, (∀ I, 0 ≤ w I) ∧
    (∀ v : V, 1 ≤ ∑ I ∈ Finset.univ.filter
        (fun I : Finset V => G.IsIndepSet (I : Set V) ∧ v ∈ I), w I) ∧
    s = ∑ I ∈ Finset.univ.filter (fun I : Finset V => G.IsIndepSet (I : Set V)), w I}

/-! Readings of the claims. -/

/-- Theorem 1.1: arbitrarily large m with an m-vertex finite simple graph, α(G) ≤ 2,
cm(G) < m/100. `m` ranges over positive naturals with `N ≤ m`; `Fin m` is the vertex type. -/
theorem reading_thm_1_1 :
    ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ 0 < m ∧ ∃ G : SimpleGraph (Fin m),
      G.indepNum ≤ 2 ∧ (cm G : ℝ) < (m : ℝ) / 100 := sorry

/-- Corollary 1.2: arbitrarily large order m with
h(G) < 26m/75 + 2/3 < m/2 ≤ χ_f(G) ≤ χ(G).
χ(G) is `ℕ∞`-valued; the last inequality is stated as: χ(G) equals some natural k and
χ_f(G) ≤ k. -/
theorem reading_cor_1_2 :
    ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ 0 < m ∧ ∃ G : SimpleGraph (Fin m),
      (hadwiger G : ℝ) < 26 * (m : ℝ) / 75 + 2 / 3 ∧
      26 * (m : ℝ) / 75 + 2 / 3 < (m : ℝ) / 2 ∧
      (m : ℝ) / 2 ≤ fracChromatic G ∧
      ∃ k : ℕ, G.chromaticNumber = (k : ℕ∞) ∧ fracChromatic G ≤ (k : ℝ) := sorry

/-- Hadwiger's conjecture is false: not every finite nonempty simple graph has h(G) ≥ χ(G). -/
theorem reading_hadwiger_false :
    ¬ ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V),
      G.chromaticNumber ≤ (hadwiger G : ℕ∞) := sorry

end ReaderC

/-
AMBIGUITIES AND CHOICES (reader C, family O41 hadwiger)

1. Hadwiger number: the text says h(G) is the largest t with a K_t minor. I model a K_t minor
   as t nonempty, pairwise disjoint, connected branch sets (connectivity via G.induce) with an
   edge between every pair. Branch sets are Set V. The set of t is bounded by |V| and contains 0,
   so sSup is the true maximum for finite V. Lean's natural-number sSup on an empty/unbounded set
   would be junk, but neither occurs here.
2. Connected matching: edges are Sym2 V in a Finset, each an edge of G; matching means no vertex
   lies in two distinct edges; "touching" means some edge of G joins a vertex of one edge to a
   vertex of the other. cm(G) = sSup over sizes. Empty matching gives 0, so the set is nonempty.
3. Independence number: used Mathlib's G.indepNum (sSup over independent sets). For Fin m with m > 0
   this is the usual maximum; the bound is G.indepNum ≤ 2.
4. Arbitrarily large m: stated as for every N there is m with N ≤ m and 0 < m (nonempty), the vertex
   type being Fin m. I added 0 < m to respect "finite nonempty".
5. Fractional chromatic number: defined as an sInf over nonnegative weight functions on all finsets
   of V, with covering constraints and total weight restricted to independent sets (the text's
   I(G)). Needs Fintype V and classical decidability (open Classical). Nonempty since unit weights
   on singletons are feasible, so the sInf is not junk for nonempty V.
6. Corollary 1.2 chromatic part: χ(G) is ℕ∞-valued in Mathlib. The chain χ_f(G) ≤ χ(G) is encoded as
   "χ(G) = k for some natural k, and χ_f(G) ≤ k"; this excludes χ = ⊤, which is harmless since the
   corollary asserts finiteness via the construction. The inequality h(G) < 26m/75 + 2/3 < m/2 is
   stated in ℝ with h cast from ℕ.
7. Hadwiger's conjecture: quantified over all types V with Fintype and Nonempty (so finite nonempty
   simple graphs up to the choice of vertex type); chromatic number is Mathlib's G.chromaticNumber,
   compared to h cast to ℕ∞. Theorem 3 is the negation of the conjecture.
8. Not formalized: the fractional weakening χ_f ≤ h is only mentioned in the text, not requested
   as a separate theorem, so it is omitted (its failure follows from the corollary).
-/
