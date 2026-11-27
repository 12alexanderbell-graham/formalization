import Mathlib

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
