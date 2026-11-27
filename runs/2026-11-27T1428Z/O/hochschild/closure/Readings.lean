import Mathlib

/-! # Target O, family hochschild: the three blind readings of run 2026-11-27T1428Z (brief 35bb25e), concatenated unchanged
apart from the repeated `import Mathlib` lines, so a closure can import them as one module. -/


/-!
Blind reading A of O54, "The Kadison–Ringrose cohomology conjecture", Theorem 1.1.
-/

namespace ReaderA

open BigOperators

variable {M : Type*} [CStarAlgebra M]

/-- Given `a = (a₁, …, a_{k+1})` (0-indexed as `a 0, …, a k`) and `j : Fin k`
(0-indexed, standing for the 1-indexed `j+1 ∈ {1,…,k}`), the `k`-tuple
`(a₁, …, a_{j} a_{j+1}, …, a_{k+1})` in which the adjacent entries in 0-indexed positions
`j` and `j+1` are multiplied. -/
def mergeAt {k : ℕ} (a : Fin (k + 1) → M) (j : Fin k) : Fin k → M := fun i =>
  if (i : ℕ) < (j : ℕ) then a i.castSucc
  else if (i : ℕ) = (j : ℕ) then a i.castSucc * a i.succ
  else a i.succ

/-- The Hochschild differential of the text, eq. (differential), on the underlying function of
a `k`-cochain:
`(df)(a₁,…,a_{k+1}) = a₁ f(a₂,…,a_{k+1})
   + ∑_{j=1}^{k} (-1)^j f(a₁,…,a_j a_{j+1},…,a_{k+1})
   + (-1)^{k+1} f(a₁,…,a_k) a_{k+1}`.
The sum index `j : Fin k` is 0-indexed, so the sign `(-1)^j` of the text is `(-1)^(j+1)`. -/
def hochschildD {k : ℕ} (f : (Fin k → M) → M) : (Fin (k + 1) → M) → M := fun a =>
  a 0 * f (fun i => a i.succ)
    + ∑ j : Fin k, ((-1 : ℂ) ^ ((j : ℕ) + 1)) • f (mergeAt a j)
    + ((-1 : ℂ) ^ (k + 1)) • (f (fun i => a i.castSucc) * a (Fin.last k))

/-- `C_b^k(M,M)`: bounded complex `k`-linear maps `M^k → M`. For multilinear maps between
normed spaces, bounded = continuous, so this is Mathlib's `ContinuousMultilinearMap`. -/
abbrev Cb (M : Type*) [CStarAlgebra M] (k : ℕ) : Type _ :=
  ContinuousMultilinearMap ℂ (fun _ : Fin k => M) M

/-- Theorem 1.1. Let `M` be a complex von Neumann algebra and `k ≥ 2`, written `k = n + 1`
with `n ≥ 1`. Every `f ∈ C_b^k(M,M)` with `df = 0` is `dg` for some `g ∈ C_b^{k-1}(M,M)`. -/
theorem reading_hochschild_main (M : Type*) [CStarAlgebra M] [WStarAlgebra M]
    (n : ℕ) (hn : 1 ≤ n) (f : Cb M (n + 1)) (hf : hochschildD (⇑f) = 0) :
    ∃ g : Cb M n, (⇑f : (Fin (n + 1) → M) → M) = hochschildD (⇑g) := sorry

end ReaderA

/-!
Ambiguities and choices.

1. "Complex von Neumann algebra M": taken abstractly, as Mathlib's `WStarAlgebra M` on top of
   a (unital) `CStarAlgebra M` (a C⋆-algebra with a Banach-space predual, Sakai's definition).
   The concrete alternative (`VonNeumannAlgebra H`, a double-commutant ⋆-subalgebra of `B(H)`)
   is equivalent mathematically; the source names no Hilbert space, so the abstract form is
   the more literal reading. "Complex" is built into `CStarAlgebra` (`NormedAlgebra ℂ`).
2. "Bounded complex k-linear maps": `ContinuousMultilinearMap ℂ (fun _ : Fin k => M) M`;
   bounded ⟺ continuous for multilinear maps on normed spaces. The norm on `C_b^k` given in
   the text is Mathlib's operator norm on this type, but it plays no role in the statement.
   No complete-boundedness is imposed, as the text says.
3. The differential is defined on the underlying function `(Fin k → M) → M` (so I do not need
   to prove that `df` is again bounded); "df = 0" is the equality of functions
   `hochschildD ⇑f = 0`, and "f = dg" is `⇑f = hochschildD ⇑g`. Index conventions: the text's
   `a_1,…,a_{k+1}` are `a 0,…,a k`; the text's `j = 1..k` is `j : Fin k` with `j+1`
   the 1-indexed value, so the sign `(-1)^j` becomes `(-1)^(j.val+1)`. Signs are computed in
   `ℂ` and act by scalar multiplication.
4. `k ≥ 2` and `g ∈ C_b^{k-1}`: to avoid ℕ subtraction `k - 1` (and a type cast between
   `Fin k` and `Fin (k-1+1)`), I write `k = n + 1` with `n ≥ 1`, so `f ∈ C_b^{n+1}` and
   `g ∈ C_b^n`. Since `n ≥ 1`, only the `k ≥ 1` formula of the differential is ever used;
   the separate degree-zero formula `(db)(a) = ab − ba` (which happens to agree with
   `hochschildD` at `k = 0`) is not needed.
5. The "Consequently `H_b^k(M,M) = 0`" sentence is a restatement (kernel/actual image, no
   closure) of the first sentence; I formalize only the first sentence, which is exactly
   `ker d ⊆ im d` in degree `k`, with the actual (non-closed) image.
6. Junk values: no ℕ subtraction (see 4), no division, no sup/inf, no extended reals.
-/


namespace ReaderB

open scoped BigOperators

variable {M : Type*} [CStarAlgebra M] [WStarAlgebra M]

/-- The Hochschild differential of the text, on an arbitrary function `f : M^k → M`
(indexed by `Fin k → M`), producing a function on `M^(k+1)`:
(df)(a₁..a_{k+1}) = a₁ f(a₂..a_{k+1}) + Σ_{j=1}^k (-1)^j f(a₁,..,a_j a_{j+1},..,a_{k+1})
                    + (-1)^{k+1} f(a₁..a_k) a_{k+1}.
Here `j : Fin k` is 0-based (text j = j+1), so the sign is (-1)^(j+1). -/
def dRaw {k : ℕ} (f : (Fin k → M) → M) : (Fin (k + 1) → M) → M := fun a =>
  a 0 * f (fun i => a i.succ)
  + ∑ j : Fin k, ((-1 : ℤ) ^ ((j : ℕ) + 1)) •
      f (fun i : Fin k =>
        if (i : ℕ) < (j : ℕ) then a i.castSucc
        else if i = j then a j.castSucc * a j.succ
        else a i.succ)
  + ((-1 : ℤ) ^ (k + 1)) • (f (fun i => a i.castSucc) * a (Fin.last k))

/-- Bounded complex `k`-linear maps `M^k → M` (for multilinear maps, continuity = boundedness),
with the operator norm of the text carried by `ContinuousMultilinearMap`. -/
abbrev Cb (M : Type*) [CStarAlgebra M] (k : ℕ) : Type _ :=
  ContinuousMultilinearMap ℂ (fun _ : Fin k => M) M

/-- Theorem 1.1, with `k = n + 2 ≥ 2`: every bounded `k`-cochain `f` with `df = 0` is `dg`
for a bounded `(k-1)`-cochain `g`. -/
theorem readingHochschild (n : ℕ) (f : Cb M (n + 2)) (hf : dRaw (⇑f) = 0) :
    ∃ g : Cb M (n + 1), dRaw (⇑g) = ⇑f := sorry

end ReaderB

/-
Ambiguities and choices.
* "Complex von Neumann algebra": taken abstractly as a W*-algebra, `[CStarAlgebra M] [WStarAlgebra M]`
  (C*-algebra with a Banach predual). This is the standard abstract equivalent of a von Neumann
  algebra on a Hilbert space (and is more general in universe terms). Unital is automatic
  (CStarAlgebra is unital).
* Bounded k-linear maps: `ContinuousMultilinearMap ℂ (Fin k → M) M`; on normed spaces a multilinear
  map is continuous iff bounded, and the norm is the sup over the unit balls as in the text.
* Differential: Mathlib has no differential on such maps and building a continuous multilinear map
  needs proofs, so `dRaw` is defined on raw functions (Fin k → M) → M, and the theorem says that the
  raw differential of the coerced g equals the coerced f. Hypothesis df = 0 is `dRaw ⇑f = 0` as
  functions. This avoids needing to prove d f is bounded multilinear; it is a fact in the text
  (d maps C_b^k to C_b^{k+1}), not part of the claim being read.
* 0-based indexing: text j=1..k becomes j : Fin k with sign (-1)^(j+1); product slot j,j+1 merged
  via an if-then-else on index (i < j: a i; i = j: a j * a (j+1); i > j: a (i+1)).
* Degree: k ≥ 2 written k = n+2, g of degree n+1, so no ℕ subtraction. Signs are integer powers
  acting by ℤ-scalar multiplication, so no junk. The statement "Consequently H^k = 0" is not stated
  separately (it is a restatement); degree-0 convention (db)(a)=ab-ba is not used (dRaw at k=0
  agrees with it anyway).
* Complete-boundedness is not imposed, as in the text.
-/


namespace ReaderC

/-- Commutant of a set `S` of bounded operators on `H`: all `T` commuting with every `x ∈ S`. -/
def commSet (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H) :=
  {T | ∀ x ∈ S, x * T = T * x}

/-- A complex von Neumann algebra on `H`: a unital `*`-subalgebra `M ⊆ B(H)` equal to its
double commutant `M'' = M`. -/
def IsVNA (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : StarSubalgebra ℂ (H →L[ℂ] H)) : Prop :=
  commSet H (commSet H (M : Set (H →L[ℂ] H))) = (M : Set (H →L[ℂ] H))

/-- Bounded `k`-linear map `M^k → M`: a `ℂ`-multilinear map with
`‖f(a_1,…,a_k)‖ ≤ C · ∏ ‖a_i‖` for some constant `C`. Norms are operator norms in `B(H)`. -/
def IsBoundedMultilinear (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : StarSubalgebra ℂ (H →L[ℂ] H)) {k : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin k => ↥M) ↥M) : Prop :=
  ∃ C : ℝ, ∀ a : Fin k → ↥M,
    ‖((f a : ↥M) : H →L[ℂ] H)‖ ≤ C * ∏ i, ‖((a i : ↥M) : H →L[ℂ] H)‖

/-- Merge the adjacent entries at positions `t` and `t+1` of `a : Fin (k+1) → R` into one
product, giving a list of length `k`. In 0-based indexing this is
`(a_0, …, a_{t-1}, a_t a_{t+1}, a_{t+2}, …)`. -/
def mergeAt {R : Type} [Mul R] {k : ℕ} (t : Fin k) (a : Fin (k+1) → R) : Fin k → R :=
  fun i =>
    if i.val < t.val then a i.castSucc
    else if i.val = t.val then a t.castSucc * a t.succ
    else a i.succ

/-- The Hochschild differential on `k`-cochains `f : (Fin k → R) → R`, written 0-based:
`(df)(a_0,…,a_k) = a_0 f(a_1,…,a_k) + ∑_{t=0}^{k-1} (-1)^{t+1} f(merge_t a)
                    + (-1)^{k+1} f(a_0,…,a_{k-1}) a_k`.
For `k = 0` this is `(db)(a) = a b - b a`, matching the text's degree-zero formula. -/
def hdiff {R : Type} [Ring R] [Algebra ℂ R] (k : ℕ) (f : (Fin k → R) → R) :
    (Fin (k+1) → R) → R :=
  fun a =>
    a 0 * f (fun i => a i.succ)
      + ∑ t : Fin k, ((-1 : ℂ) ^ (t.val + 1)) • f (mergeAt t a)
      + ((-1 : ℂ) ^ (k + 1)) • (f (fun i => a i.castSucc) * a (Fin.last k))

/-- Theorem 1.1 (Hochschild, complex von Neumann algebra `M`, degree `k = m+2 ≥ 2`):
every bounded `k`-cochain `f` with `df = 0` is `dg` for a bounded `(k-1)`-cochain `g`.
The degree is written as `m+2` to avoid natural-number subtraction, so `k-1 = m+1`. -/
theorem reading_hochschild (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : StarSubalgebra ℂ (H →L[ℂ] H)) (hM : IsVNA H M)
    (m : ℕ) (f : MultilinearMap ℂ (fun _ : Fin (m + 2) => ↥M) ↥M)
    (hf : IsBoundedMultilinear H M f)
    (hdf : ∀ a : Fin (m + 3) → ↥M, hdiff (m + 2) (⇑f) a = 0) :
    ∃ g : MultilinearMap ℂ (fun _ : Fin (m + 1) => ↥M) ↥M,
      IsBoundedMultilinear H M g ∧
        ∀ a : Fin (m + 2) → ↥M, f a = hdiff (m + 1) (⇑g) a := by
  sorry

end ReaderC

/-!
## Comment block: ambiguities and choices (reader C, family O54 / Hochschild)

1. "Complex von Neumann algebra". I used the concrete definition: a `StarSubalgebra ℂ (B(H))`
   for a complex Hilbert space `H`, equal to its double commutant (`IsVNA`). Abstract W*-algebras
   (no ambient `H`) are not covered; the bicommutant theorem is not used. The unit is
   automatic, since the double commutant contains `1`. I did not add a separate unit hypothesis.
2. Cochains. "Bounded complex `k`-linear maps `M^k → M`" is `MultilinearMap ℂ` with values in
   `↥M`. Boundedness is `∃ C, ∀ a, ‖f a‖ ≤ C ∏ ‖a_i‖`. For multilinear maps this is
   equivalent to the text's finite supremum over the closed unit ball, and it is the "ordinary
   operator-norm boundedness" the text says it means. No complete-boundedness is imposed.
3. Differential. Indexing is 0-based: the text's `a_1,…,a_{k+1}` are `a 0,…,a k`. The inner
   sum term `(-1)^j f(a_1,…,a_j a_{j+1},…)` (1-based j) is `t = j-1 : Fin k`, sign
   `(-1)^(t+1)`, merging 0-based positions `t` and `t+1`, as in `mergeAt`. The two end terms
   are `a_1 f(a_2,…)` and `(-1)^{k+1} f(a_1,…,a_k) a_{k+1}`. I took `hdiff` on `(Fin k → R) → R`
   and not on `MultilinearMap`, and I did not prove that `d` preserves multilinearity. Cochains
   are `⇑f` with the multilinear-ness carried by `f`.
4. Degree-zero differential. The formula with `k = 0` gives `a_0 f() - f() a_0`, i.e. the text's
   `ab - ba`. The theorem only uses `k ≥ 2`, so this is not needed in the statement.
5. Degrees and natural numbers. The theorem is over `k = m+2` (so `k ≥ 2` is built in), and the
   primitive has degree `m+1 = k-1`. This avoids `ℕ` subtraction. Types `Fin (m+3)` and `Fin (m+2)`
   are the domains of `hdiff (m+2) f` and `hdiff (m+1) g`; they agree with `Fin (k+1)` and `Fin k`
   by definition.
6. Equation `df = 0`. Stated as `∀ a, hdiff (m+2) f a = 0`, i.e. pointwise zero on all
   `(m+3)`-tuples. The conclusion `f = dg` is stated pointwise as `∀ a, f a = hdiff (m+1) g a`.
7. Not included. The text's "Consequently `H_b^k(M,M) = 0`" and the Kadison–Ringrose inner-
   derivation part are not in the statement. The brief asked only for the `df = 0 ⇒ f = dg`
   claim.
8. Junk values. No ℕ subtraction, division, `sSup`, `sInf` or `⊤` appears.
9. Mathlib names used: `StarSubalgebra`, `MultilinearMap`, `Fin`, and the operator-norm instances
   on `H →L[ℂ] H`. No Mathlib theorem bodies were used.
-/
