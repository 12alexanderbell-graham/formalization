import Mathlib

open Filter Asymptotics

namespace ReaderB

abbrev P : Type := EuclideanSpace ℝ (Fin 2)

/-- u(X): number of unordered pairs {x,y} ⊆ X with ‖x-y‖₂ = 1 (as a set of `Sym2` elements). -/
noncomputable def u (X : Finset P) : ℕ :=
  {z : Sym2 P | ∃ x ∈ X, ∃ y ∈ X, z = s(x, y) ∧ dist x y = 1}.ncard

/-- u(n) = max over n-point subsets of ℝ². -/
noncomputable def un (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ X : Finset P, X.card = n ∧ u X = k}

theorem reading_thm_1_1 :
    ∃ C β : ℝ, 0 < C ∧ 1 ≤ β ∧ β < 4 / 3 ∧ ∀ n : ℕ, (un n : ℝ) ≤ C * (n : ℝ) ^ β := sorry

theorem reading_equiv :
    ∃ δ : ℝ, 0 < δ ∧ (fun n : ℕ => (un n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (4 / 3 - δ)) :=
  sorry

end ReaderB

/-
Ambiguities / choices
- ℝ² is `EuclideanSpace ℝ (Fin 2)`, whose `dist` is the Euclidean (ℓ²) distance.
- Finite sets as `Finset`; |X| = n is `X.card = n`. Unordered pairs as `Sym2`; s(x,y) with dist = 1 forces x ≠ y,
  so endpoints are distinct automatically and each pair is counted once.
- u(n) is a max; defined as `sSup` in ℕ of the set of values. Junk risk: sSup on ℕ gives 0 if unbounded,
  but the set is bounded (≤ n², and nonempty since ℝ² has n-point sets), so it is the true max. Not proved.
- n ranges over all naturals including 0 (0^β = 0 for β ≥ 1, and u(0)=0, consistent with the source).
- "Absolute constants" = existential over reals C, β with 0<C, 1≤β<4/3, not depending on n.
- Equivalent form: ∃ δ>0 with u(n)=O(n^{4/3-δ}) as n→∞ (atTop on ℕ), real rpow. I state it as a separate
  existence statement; the equivalence of the two is not formalised as an iff.
-/
