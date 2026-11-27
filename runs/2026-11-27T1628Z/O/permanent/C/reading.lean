import Mathlib

/-!
Reader C, family O61: cubic lower bound for border determinantal complexity of the permanent.

Definitions are written from the text (abstract and introduction, lines 1-65).

Ambiguities and choices:
* Variables: the permanent `per_m(X)` is a polynomial in the `m²` variables indexed by
  `Fin m × Fin m`. Determinantal and border determinantal complexity are defined for
  polynomials in an arbitrary finite index type `ι` of variables.
* `per_m = ∑_{σ ∈ S_m} ∏_i x_{i,σ(i)}`, with `σ : Equiv.Perm (Fin m)`.
* Determinantal form: for `A₀, …, A_N ∈ Mat_n(ℂ)` (with `N` replaced by the index set `ι`),
  the polynomial is `det(A₀ + ∑_j x_j A_j)`, computed as `Matrix.det` over `MvPolynomial ι ℂ`.
  The size `n` is a natural number, and the set `detSet ι n` is all such polynomials.
* `dc(f)` is the least positive `n` with `f ∈ detSet ι n`. A bound "`dc(f) ≥ B`" is stated as
  "every positive `n` with `f ∈ detSet ι n` satisfies `n ≥ B`". This is equivalent to the
  least-element formulation whenever some `n` works. `Nat.find` is avoided, so there is no
  junk value, and the statement is not vacuous when the set is nonempty.
* Border determinantal complexity: `f ∈ closure(detSet ι n)` in the coefficientwise topology is
  encoded as "there is a sequence `g k ∈ detSet ι n` whose coefficients converge to those of `f`,
  monomial by monomial". The index set `ι →₀ ℕ` of monomials is countable for finite `ι`, so the
  coefficient product topology is first countable and sequential closure equals closure.
  Polynomials of degree larger than `n` cannot occur in the closure, because all `g k` have
  degree at most `n` and coefficientwise limits preserve vanishing.
* Constants: `c = 1/(5 529 600 e)` is `1 / (5529600 * Real.exp 1)` in `ℝ`, and `m₀ = 1408`.
  The theorem is stated for every `m ≥ 1408`, with the bound `c m³ ≤ n` for every admissible `n`.
* The "same numerical bound for exact determinantal complexity" is stated with `Matrix.det`
  equality `per_m = det(A₀ + ∑ x_j A_j)` in place of the closure.
* The constant `c` is absolute and explicit, so no existential quantifier is needed.
-/

namespace ReaderC

open Filter Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The permanent `per_m(X) = ∑_{σ ∈ S_m} ∏_i x_{i,σ(i)}` over the `m²` variables `(i, j)`. -/
noncomputable def perPoly (m : ℕ) : MvPolynomial (Fin m × Fin m) ℂ :=
  ∑ σ : Equiv.Perm (Fin m), ∏ i : Fin m, MvPolynomial.X (i, σ i)

/-- The polynomial `det(A₀ + ∑_j x_j A_j)` in the variables `ι`, for matrices of size `n`. -/
noncomputable def detForm {n : ℕ} (A₀ : Matrix (Fin n) (Fin n) ℂ)
    (A : ι → Matrix (Fin n) (Fin n) ℂ) : MvPolynomial ι ℂ :=
  (Matrix.of fun i j : Fin n =>
    MvPolynomial.C (A₀ i j) + ∑ k : ι, MvPolynomial.X k * MvPolynomial.C (A k i j)).det

/-- All determinantal polynomials of size `n` in the variables `ι`. -/
def detSet (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) : Set (MvPolynomial ι ℂ) :=
  {g | ∃ (A₀ : Matrix (Fin n) (Fin n) ℂ) (A : ι → Matrix (Fin n) (Fin n) ℂ),
    g = detForm A₀ A}

/-- `n` is an admissible determinantal size for `f`, that is `f = det(A₀ + ∑ x_j A_j)` with
`n` a positive integer. -/
def DCAdmissible (n : ℕ) (f : MvPolynomial ι ℂ) : Prop :=
  0 < n ∧ f ∈ detSet ι n

/-- `n` is an admissible border size for `f`: `f` is a coefficientwise limit of
determinantal polynomials of size `n`. -/
def BDCAdmissible (n : ℕ) (f : MvPolynomial ι ℂ) : Prop :=
  0 < n ∧ ∃ g : ℕ → MvPolynomial ι ℂ,
    (∀ k, g k ∈ detSet ι n) ∧
    ∀ d : ι →₀ ℕ, Tendsto (fun k => MvPolynomial.lcoeff ℂ d (g k)) atTop
      (𝓝 (MvPolynomial.lcoeff ℂ d f))

/-- Reading of Theorem 1.1: `bdc(per_m) ≥ c m³` for `m ≥ 1408`, with
`c = 1/(5 529 600 e)`. -/
theorem reading_bdc_permanent_cubic :
    ∀ m : ℕ, 1408 ≤ m → ∀ n : ℕ, BDCAdmissible n (perPoly m) →
      (1 / (5529600 * Real.exp 1)) * (m : ℝ) ^ 3 ≤ (n : ℝ) := by
  sorry

/-- Reading of the paragraph after Theorem 1.1: the same numerical bound for exact
determinantal complexity. -/
theorem reading_dc_permanent_cubic :
    ∀ m : ℕ, 1408 ≤ m → ∀ n : ℕ, DCAdmissible n (perPoly m) →
      (1 / (5529600 * Real.exp 1)) * (m : ℝ) ^ 3 ≤ (n : ℝ) := by
  sorry

end ReaderC
