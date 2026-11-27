import Mathlib

namespace ReaderC

/-- H is a real circulant Hadamard matrix of order n: entries in {-1, 1}, there are signs
h : ℤ/n → {-1, 1} with H i j = h (j - i) (indices reduced mod n via `ZMod n`), and H Hᵀ = n I. -/
def IsCirculantHadamard (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, H i j = 1 ∨ H i j = -1) ∧
  ∃ h : ZMod n → ℝ, (∀ t, h t = 1 ∨ h t = -1) ∧
    (∀ i j : Fin n, H i j = h (((j : ℤ) - (i : ℤ) : ℤ) : ZMod n)) ∧
    H * H.transpose = (n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- A Barker sequence of length n (with the entries a_0,…,a_{n-1} read from a : ℕ → ℝ; values
beyond index n-1 are irrelevant): entries ±1 and |C_a(t)| ≤ 1 for 1 ≤ t < n, where
C_a(t) = ∑_{j=0}^{n-t-1} a_j a_{j+t}. -/
def IsBarker (n : ℕ) (a : ℕ → ℝ) : Prop :=
  (∀ j, j < n → a j = 1 ∨ a j = -1) ∧
  ∀ t : ℕ, 1 ≤ t → t < n → |∑ j ∈ Finset.range (n - t), a j * a (j + t)| ≤ 1

/-- Theorem 1.1: for n > 0, a real circulant Hadamard matrix of order n exists iff n ∈ {1, 4}. -/
theorem readingC_circulant_hadamard (n : ℕ) (hn : 0 < n) :
    (∃ H : Matrix (Fin n) (Fin n) ℝ, IsCirculantHadamard n H) ↔ (n = 1 ∨ n = 4) :=
  sorry

/-- Corollary 1.2: for n > 1, a Barker sequence of length n exists iff n ∈ {2,3,4,5,7,11,13}. -/
theorem readingC_barker_lengths (n : ℕ) (hn : 1 < n) :
    (∃ a : ℕ → ℝ, IsBarker n a) ↔
      (n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 11 ∨ n = 13) :=
  sorry

end ReaderC

/-
Ambiguities and choices (reader C):
* Circulant: H_ij = h_{j-i mod n} is encoded with `h : ZMod n → ℝ` and the index
  `((j : ℤ) - (i : ℤ) : ZMod n)`, so the reduction mod n is explicit and no ℕ subtraction or
  `Fin` wrap-around is used. For n > 0 this is exactly the source's convention.
* Signs: the source's "entries in {-1,1}" is stated directly on H and also on h (the second is
  implied by the first for a circulant matrix; kept for literalness).
* Hadamard condition: H Hᵀ = n I (the source's definition), not via periodic autocorrelations.
* Barker: the sequence is a : ℕ → ℝ, read on indices < n, avoiding `Fin n` arithmetic. The
  autocorrelation sum is over `Finset.range (n - t)` with 1 ≤ t < n, so `n - t` is never truncated.
  Values are real ±1 (not ℤ) so the matrix and sequence types match the source's real setting.
* Corollary 1.2 is stated with the explicit list n = 2 ∨ n = 3 ∨ … ∨ n = 13 (the source's set).
* Theorem 1.1 assumes 0 < n as the source does.
-/
