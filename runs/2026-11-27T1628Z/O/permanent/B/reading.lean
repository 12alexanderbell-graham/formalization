import Mathlib

open MvPolynomial

namespace ReaderB

/-- The permanent polynomial per_m in the variables x_{ij}. -/
noncomputable def per (m : ℕ) : MvPolynomial (Fin m × Fin m) ℂ :=
  ∑ σ : Equiv.Perm (Fin m), ∏ i : Fin m, X (i, σ i)

section
variable {ι : Type} [Fintype ι]

/-- The affine-linear matrix A₀ + ∑_j x_j A_j over the polynomial ring. -/
noncomputable def affineMat (n : ℕ) (A₀ : Matrix (Fin n) (Fin n) ℂ)
    (A : ι → Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) (MvPolynomial ι ℂ) :=
  fun i k => C (A₀ i k) + ∑ j, C (A j i k) * X j

/-- The set (eq:border-definition): determinants of order-n affine-linear matrices. -/
def detSet (n : ℕ) : Set (MvPolynomial ι ℂ) :=
  {f | ∃ (A₀ : Matrix (Fin n) (Fin n) ℂ) (A : ι → Matrix (Fin n) (Fin n) ℂ),
    f = (affineMat n A₀ A).det}

/-- Coefficientwise topology: induced from the product topology on coefficient functions
`(ι →₀ ℕ) → ℂ`. -/
noncomputable abbrev coeffTop : TopologicalSpace (MvPolynomial ι ℂ) :=
  TopologicalSpace.induced (fun f (m : ι →₀ ℕ) => MvPolynomial.coeffAddMonoidHom m f) inferInstance

/-- Coefficientwise closure of `detSet n`. -/
def borderSet (n : ℕ) : Set (MvPolynomial ι ℂ) :=
  @closure _ coeffTop (detSet n)

/-- `dc f ≤ n`-style membership: f ∈ detSet n. `bdc`: f ∈ borderSet n.
"dc(f) ≥ B" means: every positive n with f ∈ detSet n satisfies B ≤ n (similarly for bdc). -/
def DCAtLeast (f : MvPolynomial ι ℂ) (B : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → f ∈ detSet n → B ≤ n

def BDCAtLeast (f : MvPolynomial ι ℂ) (B : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → f ∈ borderSet n → B ≤ n
end

/-- Theorem 1.1, existential form. -/
theorem readingThm1_1 :
    ∃ (c : ℝ) (m₀ : ℕ), 0 < c ∧ ∀ m : ℕ, m₀ ≤ m → BDCAtLeast (per m) (c * (m : ℝ) ^ 3) := sorry

/-- Theorem 1.1 with the stated constants. -/
theorem readingThm1_1_explicit :
    ∀ m : ℕ, 1408 ≤ m →
      BDCAtLeast (per m) ((1 / (5529600 * Real.exp 1)) * (m : ℝ) ^ 3) := sorry

/-- Next paragraph: same numerical bound for exact determinantal complexity. -/
theorem readingDC_explicit :
    ∀ m : ℕ, 1408 ≤ m →
      DCAtLeast (per m) ((1 / (5529600 * Real.exp 1)) * (m : ℝ) ^ 3) := sorry

/-
Ambiguities and choices.
* Variables: the text uses x_1..x_N; I use any finite index type ι (here Fin m × Fin m for per_m),
  with MvPolynomial ι ℂ.
* dc(f), bdc(f) are "least positive n such that ...". To avoid Nat.find / sInf, I state the lower
  bound as: every n ≥ 1 for which f lies in the set (resp. its closure) satisfies B ≤ n.
  This is equivalent to bdc(f) ≥ B whenever the least n exists (it does, by Valiant's theorem,
  but nothing in my statement depends on that; if no n existed the claim would be vacuous,
  which is why one should keep in mind the existence is not asserted here).
* Closure: topological closure in the topology induced from coefficient functions
  (ι →₀ ℕ) → ℂ with the product topology. The text takes closure in the finite-dimensional space
  of polynomials of degree ≤ n; detSet n lies in that subspace, which is closed in my topology
  and carries the usual finite-dimensional topology there, so closures agree. Polynomials of
  larger degree are therefore automatically excluded. Zariski closure not used.
* Matrix entries: Matrix (Fin n) (Fin n) (MvPolynomial ι ℂ), determinant `Matrix.det`.
  Order n is fixed along approximations (closure of the fixed-n set).
* Constants: c = 1/(5529600 e) with Real.exp 1 > 0 (no division by zero), m₀ = 1408; the
  numeric bound c m³ is real, cast of m to ℝ; comparison B ≤ (n:ℝ).
* The existential version (absolute c > 0, m₀) is also given. The ABP consequences in the
  abstract are not formalized (not requested).
* Junk: no ℕ subtraction, no sInf/Nat.find, no log/sqrt used.
-/

end ReaderB
