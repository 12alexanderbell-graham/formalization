import Mathlib

namespace ReaderA

open Finset

variable {V : Type*} [Fintype V]

/-- `G` contains a `K_t` minor: `t` pairwise disjoint branch sets, each inducing a connected
(hence nonempty) subgraph, with an edge of `G` between any two distinct branch sets. -/
def HasCliqueMinor (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ B : Fin t → Set V,
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
    (∀ i, (G.induce (B i)).Connected) ∧
    (∀ i j, i ≠ j → ∃ u ∈ B i, ∃ v ∈ B j, G.Adj u v)

open Classical in
/-- Hadwiger number `h(G)`: the largest `t` such that `G` has a `K_t` minor.
Branch sets are disjoint and nonempty, so `t ≤ |V|`; hence `findGreatest` up to `|V|`
is the genuine maximum (and `t = 0` always qualifies). -/
noncomputable def hadwiger (G : SimpleGraph V) : ℕ :=
  Nat.findGreatest (HasCliqueMinor G) (Fintype.card V)

open Classical in
/-- The family `𝓘(G)` of independent vertex sets. -/
noncomputable def indepSets (G : SimpleGraph V) : Finset (Finset V) :=
  Finset.filter (fun s : Finset V => G.IsIndepSet (↑s : Set V)) Finset.univ

/-- Independence number `α(G)`: maximum size of an independent vertex set
(the empty set is independent, so the maximum over a nonempty finite family). -/
noncomputable def indepNumber (G : SimpleGraph V) : ℕ :=
  (indepSets G).sup Finset.card

open Classical in
/-- Chromatic number `χ(G)` as a natural number: least `n` with a proper `n`-coloring.
Exists since `G` is `|V|`-colorable, so no `⊤` / junk value. -/
noncomputable def chromatic (G : SimpleGraph V) : ℕ :=
  Nat.find (⟨Fintype.card V, G.colorable_of_fintype⟩ : ∃ n, G.Colorable n)

/-- Two disjoint edges `e, f` are touching if some edge of `G` joins their endpoint sets. -/
def Touching (G : SimpleGraph V) (e f : Sym2 V) : Prop :=
  ∃ u ∈ e, ∃ v ∈ f, G.Adj u v

/-- A connected matching: a set of edges of `G`, pairwise disjoint (a matching), and
pairwise touching. -/
def IsConnectedMatching (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v, v ∈ e → v ∉ f) ∧
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f → Touching G e f)

open Classical in
/-- `cm(G)`: maximum size of a connected matching (the empty matching qualifies). -/
noncomputable def cm (G : SimpleGraph V) : ℕ :=
  ((univ : Finset (Finset (Sym2 V))).filter (fun M => IsConnectedMatching G M)).sup
    Finset.card

open Classical in
/-- A fractional coloring: nonnegative weights `w_I` on `I ∈ 𝓘(G)` with
`∑_{I ∋ v} w_I ≥ 1` for every vertex `v` (values of `w` off `𝓘(G)` are ignored). -/
def IsFracColoring (G : SimpleGraph V) (w : Finset V → ℝ) : Prop :=
  (∀ I ∈ indepSets G, 0 ≤ w I) ∧
  ∀ v : V, 1 ≤ ∑ I ∈ (indepSets G).filter (fun I => v ∈ I), w I

/-- Fractional chromatic number `χ_f(G)`: the minimum of `∑_I w_I` over fractional colorings.
The set is nonempty (unit weights on singletons) and bounded below by `0`, so `sInf` is
the genuine infimum (which the paper asserts is a minimum). -/
noncomputable def fracChromatic (G : SimpleGraph V) : ℝ :=
  sInf {r : ℝ | ∃ w : Finset V → ℝ, IsFracColoring G w ∧ r = ∑ I ∈ indepSets G, w I}

/-- Theorem 1.1: there are arbitrarily large integers `m` for which some `m`-vertex finite
simple graph `G` has `α(G) ≤ 2` and `cm(G) < m/100`. -/
theorem reading_thm_1_1 :
    ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ ∃ G : SimpleGraph (Fin m),
      indepNumber G ≤ 2 ∧ (cm G : ℝ) < (m : ℝ) / 100 := sorry

/-- Corollary 1.2: finite nonempty simple graphs of arbitrarily large order `m` with
`h(G) < 26m/75 + 2/3 < m/2 ≤ χ_f(G) ≤ χ(G)`. -/
theorem reading_cor_1_2 :
    ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ 0 < m ∧ ∃ G : SimpleGraph (Fin m),
      (hadwiger G : ℝ) < 26 * (m : ℝ) / 75 + 2 / 3 ∧
      26 * (m : ℝ) / 75 + 2 / 3 < (m : ℝ) / 2 ∧
      (m : ℝ) / 2 ≤ fracChromatic G ∧
      fracChromatic G ≤ (chromatic G : ℝ) := sorry

/-- Hadwiger's conjecture is false: not every finite nonempty simple graph has `h(G) ≥ χ(G)`. -/
theorem reading_hadwiger_false :
    ¬ ∀ (W : Type) [Fintype W] [Nonempty W] (G : SimpleGraph W),
      chromatic G ≤ hadwiger G := sorry

end ReaderA

/-
AMBIGUITIES AND CHOICES (reader A)

1. Minor / Hadwiger number. The text says only "largest t for which G contains a K_t minor".
   I used the branch-set characterisation (as in the companion paper's own phrasing:
   disjoint connected sets, every two joined by an edge). Connectedness is
   `(G.induce (B i)).Connected`, which in Mathlib includes nonemptiness, so empty branch sets
   are excluded. `h` is `Nat.findGreatest` up to `|V|`; since disjoint nonempty branch sets
   force `t ≤ |V|`, this is the true maximum, not a truncation; `t = 0` always qualifies,
   so there is no empty-set junk. No `sSup` used.

2. Matching / connected matching. A matching = finite set of edges of `G` that pairwise share
   no endpoint. "Touching" = some edge of `G` joins a vertex of `e` to a vertex of `f`.
   "Pairwise touching" is required for every pair of distinct matching edges (the text stresses
   this). `cm` = `Finset.sup card` over all qualifying edge sets; the empty set qualifies, so the
   max is over a nonempty family (no junk).

3. Independence number `α` defined by me as max card of a Mathlib `IsIndepSet` finset (Finset
   sup, nonempty family). Did not use Mathlib's `indepNum` (an `sSup`) to avoid any sSup issue.

4. Chromatic number: Mathlib's `chromaticNumber` is `ℕ∞`-valued; I instead take `Nat.find`
   of `G.Colorable n`, with existence witnessed by `|V|`, so no `⊤`.

5. Fractional chromatic number: weights `w : Finset V → ℝ`, only values on `𝓘(G)` matter
   (nonnegativity and the sums range over `𝓘(G)`); the empty independent set is included in
   `𝓘(G)` as in "the family of its independent vertex sets" (harmless). The text says
   "minimum"; I use `sInf` over achievable totals, which is over a nonempty, bounded-below set
   (singleton unit weights are feasible; totals ≥ 0), so it is the genuine infimum; equality with
   the minimum is LP theory and is not needed for the statements. The text defines χ_f only for
   nonempty graphs; Corollary 1.2 includes `0 < m`.

6. "Arbitrarily large integers m" read as: for every `N` there is `m ≥ N`. An "m-vertex graph"
   is taken with vertex type `Fin m` (any finite type of card m is isomorphic). Real-number
   comparisons (`m/100`, `26m/75 + 2/3`, `m/2`) are done in `ℝ` after casting, so no ℕ division
   or subtraction anywhere.

7. Corollary 1.2's chain is stated as four separate real inequalities. The middle inequality
   `26m/75 + 2/3 < m/2` is pure arithmetic (equivalent to m > 100/23, i.e. m ≥ 5), kept for
   literalness. The final "Thus ... fractional weakening χ_f(G) ≤ h(G) is false" is not stated
   separately (it follows from the chain).

8. "Hadwiger's conjecture is false": negation of `∀ finite nonempty simple graph, χ(G) ≤ h(G)`,
   quantified over `W : Type` with `[Fintype W] [Nonempty W]`. Universe fixed at `Type`
   (Theorem/Corollary only need `Fin m`).
-/
