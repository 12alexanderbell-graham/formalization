import Mathlib

/-!
Blind reading of `noncoord/sources/paper_lines25-121.tex` (family O10).
Only the brief and that TeX excerpt were used, plus Mathlib names.
-/

open MvPolynomial

noncomputable section

namespace O10Reading

/-- R = ℂ[h,u,v,w] with variable order: `X 0 = h`, `X 1 = u`, `X 2 = v`, `X 3 = w`. -/
abbrev R := MvPolynomial (Fin 4) ℂ

variable (h u v w : R)

/-- Notation from (eq:xyz), with h = X 0, u = X 1, v = X 2, w = X 3. -/
def xX : R := X 1 ^ 3 + X 0 * X 2

def yY : R := -(X 1 ^ 2) + X 0 * X 3

/-- The quotient `S` in `x^2 + y^3 = h * S`. -/
def sS : R :=
  2 * X 1 ^ 3 * X 2 + 3 * X 1 ^ 4 * X 3
    + X 0 * (X 2 ^ 2 - 3 * X 1 ^ 2 * X 3 ^ 2) + X 0 ^ 2 * X 3 ^ 3

/-- `p(x,y,s) = -2 s^2 x + 3 s y^2 - 3 s^3 y`, evaluated at the elements above. -/
def pP : R := -2 * sS ^ 2 * xX + 3 * sS * yY ^ 2 - 3 * sS ^ 3 * yY

/-- The polynomial `F = h - p(x,y,s) - 1` of (eq:F). -/
def FF : R := X 0 - pP - 1

/-- Ambiguity choice: "coordinate of R" = `f` is the image of some variable under a
ℂ-algebra automorphism of `R`. The paper says "first component"; we quantify over all
variables `i`, which is equivalent up to a permutation automorphism. -/
def IsCoordinate {n : ℕ} (f : MvPolynomial (Fin n) ℂ) : Prop :=
  ∃ φ : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ, ∃ i : Fin n, φ (X i) = f

/-- Sanity check that the derived identity `x^2 + y^3 = h * s` holds (stated, not used). -/
theorem reading_identity : xX ^ 2 + yY ^ 3 = X 0 * sS := by
  sorry

/-- R/(F) ≅ ℂ^[3]. `ℂ^[3]` is `MvPolynomial (Fin 3) ℂ`; the isomorphism is ℂ-linear
(`≃ₐ[ℂ]`) and we take `Nonempty` of it. -/
theorem reading_thm_quotient :
    Nonempty ((R ⧸ Ideal.span {FF}) ≃ₐ[ℂ] MvPolynomial (Fin 3) ℂ) := by
  sorry

/-- Every partial derivative of F vanishes at (h,u,v,w) = (2, 0, -1/2, 1/2). -/
theorem reading_thm_gradient :
    ∀ i : Fin 4, eval ![(2 : ℂ), 0, -1/2, 1/2] (pderiv i FF) = 0 := by
  sorry

/-- F is not a coordinate of R. -/
theorem reading_thm_noncoordinate : ¬ IsCoordinate FF := by
  sorry

/-- Corollary 1.2: for every n ≥ 4 there is f ∈ ℂ[z_1..z_n] with
ℂ[z]/(f) ≅ ℂ^[n-1] (ℂ-algebra iso; `n - 1` is ℕ-subtraction, harmless since n ≥ 4)
and f not a coordinate. -/
theorem reading_cor (n : ℕ) (hn : 4 ≤ n) :
    ∃ f : MvPolynomial (Fin n) ℂ,
      Nonempty ((MvPolynomial (Fin n) ℂ ⧸ Ideal.span {f}) ≃ₐ[ℂ]
        MvPolynomial (Fin (n - 1)) ℂ) ∧ ¬ IsCoordinate f := by
  sorry

end O10Reading

end

/-!
## Ambiguity notes and choices

1. Variable order: `X 0 = h, X 1 = u, X 2 = v, X 3 = w`, following the order of the
   listed variables in F ∈ ℂ[h,u,v,w]. Point `(2, 0, -1/2, 1/2)` is read in that same order.
2. ℂ^[m] is read as `MvPolynomial (Fin m) ℂ`. Isomorphisms are ℂ-algebra isomorphisms
   (`≃ₐ[ℂ]`), since the paper says the displayed isomorphism must fix ℂ. Wrapped in
   `Nonempty` (existence, no chosen map).
3. "Coordinate": f is a coordinate iff there is a ℂ-algebra automorphism φ of the
   polynomial ring with f = φ(X i) for some i. Paper says "first component"; I quantify
   over all i (equivalent up to a permutation automorphism). The brief's ambiguity about
   φ direction (φ(X i) = f vs φ(f) = X i) is equivalent since φ can be inverted.
4. Corollary `n - 1`: ℕ-subtraction. For n ≥ 4 this is the genuine value n-1 ≥ 3, so no
   truncation issue arises. The corollary is stated for the ambient ring of n variables
   `Fin n`, with the quotient ring written `MvPolynomial (Fin n) ℂ ⧸ Ideal.span {f}`.
5. Quotient: `R ⧸ Ideal.span {F}` is the ideal quotient, with its ℂ-algebra structure
   from Mathlib's `Ideal.Quotient.algebra`.
6. Partial derivatives: `MvPolynomial.pderiv i` (formal derivative), evaluated via
   `MvPolynomial.eval` at the point `![2, 0, -1/2, 1/2]`.
7. Paper's (eq:xyz)-(eq:F) lists `x, y, s` as symbols; I took `s` as the displayed
   polynomial S(h,u,v,w) (the paper says s = S), and `x, y` as the displayed polynomials.
   Hand check: x^2 + y^3 = h * S holds (verified by expansion), so no
   ambiguity there beyond the sign conventions as printed.
8. `sS`, `pP`, `FF` are defined with `def` and not `abbrev`; `variable (h u v w : R)` is
   unused and harmless (the compiler may warn about it).
9. The `reading_identity` lemma is an extra check beyond the requested four theorems.
   Left as `sorry`, as all the others.
-/
