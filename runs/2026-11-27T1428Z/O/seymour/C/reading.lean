import Mathlib

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
