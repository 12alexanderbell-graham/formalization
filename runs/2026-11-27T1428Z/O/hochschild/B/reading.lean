import Mathlib

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
