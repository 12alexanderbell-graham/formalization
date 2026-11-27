import Mathlib

/-! # Target O, family permanent: the three blind readings of run 2026-11-27T1628Z (brief da5a1fc), concatenated unchanged
apart from the repeated `import Mathlib` lines, so a closure can import them as one module. -/


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
