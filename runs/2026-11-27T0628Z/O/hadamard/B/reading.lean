import Mathlib

namespace ReaderB

/-- Real circulant Hadamard matrix of order n: signs h : ZMod n → ℝ, H i j = h (j - i), H Hᵀ = n I.
Indices are `Fin n`, cast into `ZMod n` through their ℕ value (well defined for n>0). -/
def IsCirculantHadamard (n : ℕ) : Prop :=
  ∃ h : ZMod n → ℝ, (∀ t, h t = 1 ∨ h t = -1) ∧
    let H : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => h ((j : ℕ) - (i : ℕ))
    H * H.transpose = (n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- Aperiodic autocorrelation C_a(t) = ∑_{j=0}^{n-t-1} a_j a_{j+t}, written as a sum over
{j < n | j + t < n} to avoid ℕ subtraction. -/
def aperiodicCorr (n : ℕ) (a : ℕ → ℤ) (t : ℕ) : ℤ :=
  ∑ j ∈ (Finset.range n).filter (fun j => j + t < n), a j * a (j + t)

/-- Barker sequence of length n (a_0..a_{n-1}, with a : ℕ → ℤ read on range n). -/
def IsBarker (n : ℕ) : Prop :=
  1 < n ∧ ∃ a : ℕ → ℤ, (∀ j < n, a j = 1 ∨ a j = -1) ∧
    ∀ t, 1 ≤ t → t < n → |aperiodicCorr n a t| ≤ 1

/-- Theorem 1.1. -/
theorem readingCirculantHadamard (n : ℕ) (hn : 0 < n) :
    IsCirculantHadamard n ↔ n ∈ ({1, 4} : Set ℕ) := sorry

/-- Corollary 1.2. -/
theorem readingBarker (n : ℕ) (hn : 1 < n) :
    IsBarker n ↔ n ∈ ({2, 3, 4, 5, 7, 11, 13} : Set ℕ) := sorry

end ReaderB

/-
Ambiguities / choices.
* The circulant condition H_ij = h_{(j-i) mod n} is expressed with h : ZMod n → ℝ and ZMod subtraction of
  the ℕ-casts of the Fin indices, so there is no ℕ subtraction and no Fin wrap-around; ZMod n for n>0
  is Z/n. For n = 0 the notion degenerates, so the theorem assumes 0 < n as in the source.
* Entries are real numbers with value 1 or -1; Hadamard condition H Hᵀ = n I as real matrices.
  (The source also states the equivalent autocorrelation formulation; I use the matrix definition.)
* Barker sequence: sign sequence a : ℕ → ℤ whose values on 0..n-1 are ±1 (values outside ignored); aperiodic
  correlation summed over j<n with j+t<n (the same index set as 0..n-t-1 for t<n). Condition |C(t)|≤1 for 1≤t<n.
* `IsBarker n` includes n>1; the corollary also assumes n>1.
-/
