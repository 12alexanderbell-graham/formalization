import Mathlib

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
