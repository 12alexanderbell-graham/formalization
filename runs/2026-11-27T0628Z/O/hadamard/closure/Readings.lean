import Mathlib

/-! Blind readings A, B, C (code unchanged; only `import Mathlib` hoisted). -/

-- ===== reader A =====

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

-- ===== reader B =====

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

-- ===== reader C =====

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
