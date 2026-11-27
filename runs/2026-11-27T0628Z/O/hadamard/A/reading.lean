import Mathlib

namespace ReaderA

open Matrix

/-- A real Hadamard matrix of order `n`: entries in `{-1, 1}` and `H Hᵀ = n I_n`. -/
def IsRealHadamard {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, H i j = -1 ∨ H i j = 1) ∧ H * Hᵀ = (n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- `H` is circulant: there are signs `h₀, …, h_{n-1}` with `H i j = h_{(j - i) mod n}`.
Here `j - i` is subtraction in `Fin n`, which is by definition subtraction modulo `n`
(this wrap-around is exactly the intended `mod n`). -/
def IsCirculant {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ h : Fin n → ℝ, (∀ k, h k = -1 ∨ h k = 1) ∧ ∀ i j : Fin n, H i j = h (j - i)

/-- Aperiodic autocorrelation `C_a(t) = ∑_{j=0}^{n-t-1} a_j a_{j+t}`, written as a sum over
`j : Fin n` restricted to `j + t < n` (no natural-number subtraction). -/
def aperiodicAutocorr {n : ℕ} (a : Fin n → ℤ) (t : ℕ) : ℤ :=
  ∑ j : Fin n, if h : (j : ℕ) + t < n then a j * a ⟨(j : ℕ) + t, h⟩ else 0

/-- A Barker sequence of length `n`: a sign sequence with `|C_a(t)| ≤ 1` for `1 ≤ t < n`. -/
def IsBarker {n : ℕ} (a : Fin n → ℤ) : Prop :=
  (∀ j, a j = -1 ∨ a j = 1) ∧ ∀ t : ℕ, 1 ≤ t → t < n → |aperiodicAutocorr a t| ≤ 1

/-- Theorem 1.1. -/
theorem reading_thm_1_1 (n : ℕ) (hn : 0 < n) :
    (∃ H : Matrix (Fin n) (Fin n) ℝ, IsRealHadamard H ∧ IsCirculant H) ↔ n = 1 ∨ n = 4 :=
  sorry

/-- Corollary 1.2. -/
theorem reading_cor_1_2 (n : ℕ) (hn : 1 < n) :
    (∃ a : Fin n → ℤ, IsBarker a) ↔ n ∈ ({2, 3, 4, 5, 7, 11, 13} : Finset ℕ) :=
  sorry

end ReaderA

/-
Ambiguities and choices (reader A):

1. Matrix indexing. Rows/columns indexed by `Fin n` (= 0 ≤ i, j < n as in the source).
   "Order n" is encoded by the index type `Fin n`.
2. `j - i mod n`: implemented as `Fin` subtraction `j - i : Fin n`, which Lean defines as
   `((n - i) + j) % n`, i.e. exactly `(j - i) mod n` in `{0,…,n-1}`. The wrap-around is
   the intended modular reduction, not a junk value. No natural-number subtraction is used.
3. "Signs h₀,…,h_{n-1}": the circulant definition itself requires `h k ∈ {-1,1}`; this is
   redundant given the Hadamard entry condition, but matches the source text.
4. Entries of `H` are real numbers constrained to `{-1, 1}`; `H Hᵀ = n I` uses `(n : ℝ) • 1`.
5. Barker sequence: values taken in `ℤ` (signs `±1`); `C_a(t)` defined as a sum over
   `j : Fin n` with the guard `j + t < n`, which is the same index set as `0 ≤ j ≤ n - t - 1`
   for `t < n` while avoiding truncated `ℕ` subtraction and `Fin` wrap-around in `a_{j+t}`.
   `C_a(t)` is only used for `1 ≤ t < n`.
6. The periodic autocorrelation `P_h` is not needed for the two statements and is not defined.
7. "Exists" in both statements is plain existence of a matrix / sequence of the given order /
   length; hypotheses `0 < n` and `1 < n` are kept as in the source.
-/
