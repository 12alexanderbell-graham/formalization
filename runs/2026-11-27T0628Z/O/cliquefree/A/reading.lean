import Mathlib

/-!
# Blind reading (reader A): family O11, clique-free independence bound

Source: `cliquefree/sources/introduction_lines1-25.tex`, Theorem 1.1 (`thm:main`).
-/

open Classical

namespace O11Reading

variable {V : Type} [Fintype V]

/-- "An independent set in a graph is a set of pairwise nonadjacent vertices." -/
def IsIndependent (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, ¬ G.Adj x y

/-- `α(G)`: "the largest size of an independent set". A maximum over the finite,
nonempty (it contains `∅`) family of independent subsets of the finite vertex set,
so `Finset.sup` is a genuine maximum (no `sSup` junk). -/
noncomputable def indepNum (G : SimpleGraph V) : ℕ :=
  ((Finset.univ : Finset (Finset V)).filter (fun s => IsIndependent G s)).sup Finset.card

/-- `|E(G)|`: the number of edges, i.e. of unordered pairs `{u, v}` with `u ~ v`. -/
noncomputable def numEdges (G : SimpleGraph V) : ℕ :=
  ((Finset.univ : Finset (Sym2 V)).filter (fun e => e ∈ G.edgeSet)).card

/-- Average degree `d(G) = 2|E(G)|/n`, where `n = |V|`. Only used under `0 < n`. -/
noncomputable def avgDegree (G : SimpleGraph V) : ℝ :=
  2 * (numEdges G : ℝ) / (Fintype.card V : ℝ)

/-- "`G` is `K_r`-free if no `r` vertices are pairwise adjacent." -/
def KrFree (G : SimpleGraph V) (r : ℕ) : Prop :=
  ¬ ∃ s : Finset V, s.card = r ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → G.Adj x y

/-- Theorem 1.1. For every integer `r ≥ 4` there is a constant `c_r > 0` such that every
finite simple `K_r`-free graph `G` with `n` vertices and average degree `d ≥ 2` satisfies
`α(G) ≥ c_r · n log d / d`. -/
theorem reading :
    ∀ r : ℕ, 4 ≤ r →
      ∃ c : ℝ, 0 < c ∧
        ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
          0 < Fintype.card V →
          KrFree G r →
          2 ≤ avgDegree G →
          c * ((Fintype.card V : ℝ) * Real.log (avgDegree G) / avgDegree G)
            ≤ (indepNum G : ℝ) := sorry

end O11Reading

/-
## Ambiguity notes (reader A)

1. "finite simple graph G with n vertices": modelled as Mathlib's `SimpleGraph V`
   (symmetric, irreflexive adjacency = simple, no loops/multi-edges) on an arbitrary
   `V : Type` with `[Fintype V]`; `n := Fintype.card V`. Quantifying over all finite
   types (rather than `Fin n`) is equivalent up to relabelling. The universe is fixed
   to `Type`. The `Fintype` instance is universally quantified inside the statement.
2. Decidability: `open Classical` so the filters in `indepNum`/`numEdges` need no
   `DecidableRel G.Adj` argument; this does not change any value.
3. `α(G)`: defined by me as `Finset.sup card` over the independent subsets of `univ`.
   That family is finite and contains `∅`, so this is the true maximum, not junk.
4. `|E(G)|`: counted as the number of `Sym2 V` elements in `G.edgeSet` (unordered
   adjacent pairs). Since `G` is loopless, no diagonal element is counted.
5. Average degree `d(G) = 2|E(G)|/n` is defined "if G has n > 0 vertices". I add the
   explicit hypothesis `0 < Fintype.card V`, so the division is never by zero.
   (Without it, Lean's `x/0 = 0` would make `2 ≤ d` false anyway, but I state it.)
6. `log`: "All logarithms are natural" → `Real.log`. Under `d ≥ 2`, `log d > 0` and
   `d > 0`, so neither `log` of a non-positive number nor division by zero occurs.
7. `K_r`-free: "no r vertices are pairwise adjacent; exclusion as an ordinary
   subgraph". Encoded as: no `r`-element vertex set whose distinct members are all
   adjacent. Containing `K_r` as a (not necessarily induced) subgraph is exactly this.
   I did not use Mathlib's `CliqueFree` (written from the source instead); they agree.
8. Quantifier order: `c_r` depends only on `r` (chosen before `V`, `G`), matching
   "The constant is uniform in both the number of vertices and the average degree".
9. "integer r ≥ 4": `r : ℕ` with `4 ≤ r` (an integer ≥ 4 is a natural number).
10. "satisfies α(G) ≥ c_r n log d / d": written as `c * (n * log d / d) ≤ α(G)` in `ℝ`,
    with `α(G)` cast to `ℝ`. Parenthesisation `c_r · ((n log d)/d)` is the natural
    reading of `c_r \frac{n\log d}{d}`; all groupings are equal in a field anyway.
11. Source hygiene: the source file provided is `introduction_lines1-25.tex` (an
    excerpt), so its sha256 (prefix ad7bf2900431d047) cannot be compared with the
    brief's prefix for the full `introduction.tex` (8fc8936de587ee76).
-/
