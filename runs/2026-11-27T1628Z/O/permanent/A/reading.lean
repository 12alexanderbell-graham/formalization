import Mathlib

/-!
Blind reading A of O61, "A cubic lower bound for border determinantal complexity of the
permanent": Theorem 1.1 and the claim that the same bound holds for exact determinantal
complexity. Source: abstract + introduction lines 1-65.
-/

namespace ReaderA

open MvPolynomial Topology

/-- The `m × m` permanent `per_m(X) = ∑_{σ ∈ S_m} ∏_{i} x_{i,σ(i)}` in the `m²` independent
variables `x_{ij}`, indexed by `Fin m × Fin m`. -/
noncomputable def per (m : ℕ) : MvPolynomial (Fin m × Fin m) ℂ :=
  ∑ s : Equiv.Perm (Fin m), ∏ i : Fin m, X (i, s i)

variable {ι : Type*} [Fintype ι]

/-- `det(A₀ + ∑_j x_j A_j)` as a polynomial in the variables `x_j`, `j ∈ ι`, for
`A₀, A_j ∈ Mat_n(ℂ)`. -/
noncomputable def detAffine {n : ℕ} (A₀ : Matrix (Fin n) (Fin n) ℂ)
    (A : ι → Matrix (Fin n) (Fin n) ℂ) : MvPolynomial ι ℂ :=
  ((A₀.map C) + ∑ j : ι, (X j : MvPolynomial ι ℂ) • (A j).map C).det

/-- The set (eq:border-definition): all `det(A₀ + ∑_j x_j A_j)` with `n × n` complex `A`'s. -/
def detSet (ι : Type*) [Fintype ι] (n : ℕ) : Set (MvPolynomial ι ℂ) :=
  {g | ∃ (A₀ : Matrix (Fin n) (Fin n) ℂ) (A : ι → Matrix (Fin n) (Fin n) ℂ),
    g = detAffine A₀ A}

/-- `f` has an exact determinantal representation of size `n`. -/
def HasDetRep (f : MvPolynomial ι ℂ) (n : ℕ) : Prop := f ∈ detSet ι n

/-- Coefficient vector of a polynomial, a point of `(ι →₀ ℕ) → ℂ` (product topology). -/
noncomputable def coeffVec (g : MvPolynomial ι ℂ) : (ι →₀ ℕ) → ℂ := fun d => g.coeff d

/-- `f` lies in the coefficientwise closure of `detSet ι n`: the coefficient vector of `f` is
in the closure of the coefficient vectors of `detSet ι n`, for the topology of coefficientwise
convergence (product topology on `(ι →₀ ℕ) → ℂ`). -/
def InBorder (f : MvPolynomial ι ℂ) (n : ℕ) : Prop :=
  coeffVec f ∈ closure (coeffVec '' detSet ι n)

/-- The constant `c = 1 / (5 529 600 e)`. -/
noncomputable def cPer : ℝ := 1 / (5529600 * Real.exp 1)

/-- Theorem 1.1 with the stated constants: for every integer `m ≥ 1408`,
`bdc(per_m) ≥ c m³`, `c = 1/(5 529 600 e)`. Since `bdc` is the least positive `n` with
`per_m` in the border set, this says every such `n` is `≥ c m³`. -/
theorem reading_thm_1_1 (m : ℕ) (hm : 1408 ≤ m) (n : ℕ) (hn : 0 < n)
    (h : InBorder (per m) n) : cPer * (m : ℝ) ^ 3 ≤ n := sorry

/-- Theorem 1.1, first sentence: there exist absolute constants `c > 0` and `m₀`. -/
theorem reading_thm_1_1_exists :
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ n : ℕ, 0 < n →
      InBorder (per m) n → c * (m : ℝ) ^ 3 ≤ n := sorry

/-- "The same numerical lower bound holds for exact determinantal complexity":
`dc(per_m) ≥ c m³` for `m ≥ 1408`, `c = 1/(5 529 600 e)`. -/
theorem reading_dc (m : ℕ) (hm : 1408 ≤ m) (n : ℕ) (hn : 0 < n)
    (h : HasDetRep (per m) n) : cPer * (m : ℝ) ^ 3 ≤ n := sorry

end ReaderA

/-
AMBIGUITIES AND CHOICES

1. `dc` and `bdc` are "least positive integer n such that ...". To avoid `sInf ∅ = 0` /
   `Nat.find` on a possibly empty set, the lower bound `bdc(f) ≥ B` is stated as: every
   positive `n` with `f` in the (border) set satisfies `n ≥ B`. For a nonempty set of
   naturals this is equivalent to "the least element is ≥ B". (Existence of some `n` is not
   asserted in the read text; it is classical — Valiant — and not part of this claim.
   If the set were empty, our statement is vacuously true, whereas `bdc` would be
   undefined; we note this as the only gap.)

2. `per_m` lives in `ℂ[x_{ij}]` with variables indexed by `Fin m × Fin m` (the text's
   `ℂ[x_1,…,x_N]` with `N = m²`; relabelling variables does not change `dc`/`bdc`).
   The determinantal representations use exactly these variables (one matrix `A_{ij}` per
   variable). We wrote the permanent directly from the displayed formula rather than use
   `Matrix.permanent`.

3. `det(A₀ + ∑ x_j A_j)`: entries are affine-linear forms with complex coefficients; Lean:
   `(A₀.map C + ∑ j, X j • (A j).map C).det` over `MvPolynomial ι ℂ`. `n ≥ 1` required
   ("positive integer"); the `0 × 0` determinant (= 1) is thereby excluded.

4. Coefficientwise closure: the text takes the closure in the finite-dimensional space of
   polynomials of degree ≤ n (Euclidean topology on coefficients) and says a polynomial of
   larger degree cannot belong to it. We take the closure of the coefficient vectors in the
   product topology on `(ι →₀ ℕ) → ℂ` (pointwise convergence of all coefficients). Every
   element of `detSet ι n` has total degree ≤ n, so its coefficient vectors lie in the closed
   subspace `{v | v d = 0 for |d| > n}`, which is finite-dimensional (ι finite) and on which
   the product topology is the Euclidean one. Hence the two closures coincide, and a
   polynomial of degree > n is automatically not in our closure (its coefficient vector is
   not in that closed subspace). `f` constant or zero is allowed (no restriction on `f`).
   The text says this equals Zariski closure; we used the coefficientwise (Euclidean)
   version, as defined.

5. Constants: `c = 1/(5 529 600 e)` with `e = Real.exp 1`; division by a positive real
   (no `x/0` junk). `m₀ = 1408`, `m` an integer ≥ 1408 (ℕ). Inequality compared in `ℝ`
   with `n` cast to `ℝ`. Also stated the existential first sentence of Theorem 1.1.

6. Exact dc claim (line 64): "the same numerical lower bound" read as the same `c` and the
   same `m₀ = 1408`. (It also follows from Theorem 1.1 since dc ≥ bdc, but we state it as
   given.)

7. Not formalized: the algebraic branching program consequences (lines 65-73), which the
   brief does not request; the projective orbit closure equivalence (Prop. model-equivalence),
   outside the read lines.
-/
