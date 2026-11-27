import Mathlib

namespace ReaderB

open SimpleGraph

def HasCliqueMinor {V : Type} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ B : Fin t → Set V, (∀ i, (B i).Nonempty) ∧ (∀ i, (G.induce (B i)).Connected) ∧
    Pairwise (Function.onFun Disjoint B) ∧
    ∀ i j, i ≠ j → ∃ u ∈ B i, ∃ v ∈ B j, G.Adj u v

/-- `h` is the Hadwiger number (largest clique-minor order). -/
def IsHadwigerNumber {V : Type} (G : SimpleGraph V) (h : ℕ) : Prop :=
  HasCliqueMinor G h ∧ ∀ t, HasCliqueMinor G t → t ≤ h

/-- Every list assignment with all lists of size ≥ k admits a proper coloring from the lists. -/
def ListColorable {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (κ : Type) (L : V → Finset κ), (∀ v, k ≤ (L v).card) →
    ∃ c : V → κ, (∀ v, c v ∈ L v) ∧ ∀ u v, G.Adj u v → c u ≠ c v

/-- `ℓ` is the list chromatic number: least k such that G is k-list-colorable. -/
def IsListChromaticNumber {V : Type} (G : SimpleGraph V) (ℓ : ℕ) : Prop :=
  ListColorable G ℓ ∧ ∀ k, k < ℓ → ¬ ListColorable G k

/-- The statement of Theorem 1.1 for a given constant. -/
def ListBound (C : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) (ℓ h : ℕ),
    IsListChromaticNumber G ℓ → IsHadwigerNumber G h → ℓ ≤ C * h

/-- The conclusion of Corollary 1.2 for a given constant. -/
def OrdinaryBound (C : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) (h : ℕ),
    IsHadwigerNumber G h → G.chromaticNumber ≤ ((C * h : ℕ) : ℕ∞)

theorem reading_thm_1_1 : ∃ C : ℕ, 1 ≤ C ∧ ListBound C := sorry

theorem reading_cor_1_2 : ∀ C : ℕ, 1 ≤ C → ListBound C → OrdinaryBound C := sorry

/-
Ambiguities / choices
- h(G): as in the other family; branch sets Fin t → Set V; `IsHadwigerNumber` = attained + upper bound
  (no sSup). Exists for finite nonempty G.
- ℓ(G): "least k such that every assignment with |L(v)| ≥ k is colorable": `IsListChromaticNumber`
  = k-choosable and not (k-1)-choosable-style (¬ for every smaller k), avoiding sInf. For finite nonempty G
  it exists (k = |V| works). Color type κ : Type is universally quantified (universe 0; finite lists, so
  WLOG). "Finite set of colors" = Finset κ. Lists of size ≥ k (not exactly k).
- χ(G): Mathlib `chromaticNumber : ℕ∞`; the corollary bounds it in ℕ∞ by the cast of C*h (no toNat/⊤ junk).
  The proof remark χ ≤ ℓ is not stated; Corollary 1.2 is stated as "any C satisfying Theorem 1.1's conclusion
  also gives χ ≤ C h", matching "with the constant C in Theorem 1.1" (hypothesis `1 ≤ C` kept for fidelity).
- C is ℕ ("absolute integer C ≥ 1"); C·h is ℕ multiplication, no subtraction.
- Graphs: V : Type finite nonempty, simple (SimpleGraph).
-/

end ReaderB
