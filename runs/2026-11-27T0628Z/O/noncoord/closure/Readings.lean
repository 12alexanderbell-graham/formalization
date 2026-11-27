import Mathlib

namespace ReaderA

/-!
# Blind reading A, family O10: an explicit noncoordinate polynomial with affine three-space zero fibre

Source: `noncoord/sources/paper_lines25-121.tex` (equations (eq:xyz)–(eq:F), Theorem `thm:main`,
Corollary `cor:dimension`).
-/

namespace ReadingO10A

open MvPolynomial

/-- `R = ℂ[h,u,v,w]`, with variables indexed by `Fin 4` in the order `h, u, v, w`. -/
abbrev R := MvPolynomial (Fin 4) ℂ

/-- The variable `h`. -/
noncomputable def h : R := X 0
/-- The variable `u`. -/
noncomputable def u : R := X 1
/-- The variable `v`. -/
noncomputable def v : R := X 2
/-- The variable `w`. -/
noncomputable def w : R := X 3

/-- (eq:xyz): `x = u^3 + h v`. -/
noncomputable def x : R := u ^ 3 + h * v
/-- (eq:xyz): `y = -u^2 + h w`. -/
noncomputable def y : R := -u ^ 2 + h * w
/-- (eq:xyz): `s = S(h,u,v,w) = 2u^3v + 3u^4w + h(v^2 - 3u^2w^2) + h^2w^3`. -/
noncomputable def s : R :=
  2 * u ^ 3 * v + 3 * u ^ 4 * w + h * (v ^ 2 - 3 * u ^ 2 * w ^ 2) + h ^ 2 * w ^ 3

/-- (eq:F): `p(x,y,s) = -2 s^2 x + 3 s y^2 - 3 s^3 y`, as a function of three ring elements. -/
noncomputable def p (x y s : R) : R :=
  -2 * s ^ 2 * x + 3 * s * y ^ 2 - 3 * s ^ 3 * y

/-- (eq:F): `F = h - p(x,y,s) - 1`. -/
noncomputable def F : R := h - p x y s - 1

/-- Sanity check of the source's remark `x^2 + y^3 = h s` (proved, not part of the reading). -/
example : x ^ 2 + y ^ 3 = h * s := by
  simp only [x, y, s]; ring

/-- "`f` is a coordinate": `f` is a component of a polynomial automorphism of `𝔸^n`, i.e. the
image of some variable `X i` under a `ℂ`-algebra automorphism of the polynomial ring.
(For `σ = Fin n`, `n ≥ 1`, this is equivalent to "first component", by composing with a
variable permutation.) -/
def IsCoordinate {σ : Type*} (f : MvPolynomial σ ℂ) : Prop :=
  ∃ (e : MvPolynomial σ ℂ ≃ₐ[ℂ] MvPolynomial σ ℂ) (i : σ), e (X i) = f

/-- The point `P = (2, 0, -1/2, 1/2)` in the order `(h, u, v, w)`. -/
noncomputable def P : Fin 4 → ℂ := ![2, 0, -1/2, 1/2]

/-- Theorem 1.1, first part: `R/(F) ≅ ℂ^[3]` as `ℂ`-algebras. -/
theorem reading_thm_quotient :
    Nonempty ((R ⧸ Ideal.span ({F} : Set R)) ≃ₐ[ℂ] MvPolynomial (Fin 3) ℂ) := sorry

/-- Theorem 1.1, second part: `∇F(2, 0, -1/2, 1/2) = 0`. -/
theorem reading_thm_gradient : ∀ i : Fin 4, eval P (pderiv i F) = 0 := sorry

/-- Theorem 1.1, conclusion: `F` is not a coordinate of `R`. -/
theorem reading_thm_noncoordinate : ¬ IsCoordinate F := sorry

/-- Corollary 1.2: for every integer `n ≥ 4` there is `f ∈ ℂ[z_1,…,z_n]` with
`ℂ[z_1,…,z_n]/(f) ≅ ℂ^[n-1]` and `f` not a coordinate. -/
theorem reading_cor :
    ∀ n : ℕ, 4 ≤ n → ∃ f : MvPolynomial (Fin n) ℂ,
      Nonempty ((MvPolynomial (Fin n) ℂ ⧸ Ideal.span ({f} : Set (MvPolynomial (Fin n) ℂ)))
          ≃ₐ[ℂ] MvPolynomial (Fin (n - 1)) ℂ) ∧
        ¬ IsCoordinate f := sorry

/-
## Ambiguity notes and choices

1. Variable order. `R = ℂ[h,u,v,w]` is listed in that order and the point `P = (2,0,-1/2,1/2)`
   is read in the same order: `X 0 = h`, `X 1 = u`, `X 2 = v`, `X 3 = w`. Cross-checked outside
   Lean (sympy): with this order `F(P) = -1` (matching "P lies on the fibre F = -1") and all four
   partials vanish at `P`, so the order is consistent with the text.
2. `p(x,y,s)`: read as a polynomial in three symbols, then substituted with the elements
   `x, y, s ∈ R` from (eq:xyz). I encode `p` directly as a function `R → R → R → R`; the
   substituted result is the same.
3. `s` is taken as the displayed formula `S(h,u,v,w)`, not as the abstract quotient
   `(x^2+y^3)/h`; the two agree (`example` above, proved by `ring`).
4. `ℂ^[m]` = "a polynomial ring in m independent variables" = `MvPolynomial (Fin m) ℂ`; the
   isomorphism "is required to fix ℂ", read as a `ℂ`-algebra isomorphism (`≃ₐ[ℂ]`), stated as
   `Nonempty (… ≃ₐ[ℂ] …)`.
5. `(F)` / `(f)`: the principal ideal `Ideal.span {F}`; `R/(F)` is the Mathlib quotient ring with
   its induced `ℂ`-algebra structure.
6. Gradient vanishing: `∀ i, eval P (pderiv i F) = 0` (all four formal partial derivatives,
   evaluated at `P`), rather than a vector equation.
7. "Coordinate" = "first component of a polynomial automorphism of 𝔸^n". Encoded as: there is a
   `ℂ`-algebra automorphism `e` of the polynomial ring and a variable index `i` with
   `e (X i) = f`. A polynomial automorphism `(f_1,…,f_n)` of `𝔸^n` corresponds to the algebra
   automorphism `X j ↦ f_j`, so `f` is its first component iff `e (X 0) = f`; allowing any `i`
   is equivalent (compose with a permutation of variables) and avoids needing `0 : Fin n`.
   (Whether the automorphism is the comorphism or its inverse doesn't matter: both are
   automorphisms.)
8. ℕ subtraction in `n - 1`: harmless since the corollary quantifies over `n ≥ 4`, so `n - 1` is
   the true predecessor. `ℂ[z_1,…,z_n]` is `MvPolynomial (Fin n) ℂ` (0-indexed).
9. The corollary is stated purely existentially, as in the source; the construction
   ("adjoining variables" to F) from the abstract is not part of the statement.
10. "Consequently" in Theorem 1.1: the noncoordinate claim is stated as its own theorem, not as
    an implication from the gradient claim.
-/

end ReadingO10A
end ReaderA

namespace ReaderB

open MvPolynomial

noncomputable section

namespace ReadingB

/-- The ring R = ℂ[h,u,v,w]; variables indexed by Fin 4 as h=0, u=1, v=2, w=3. -/
abbrev R := MvPolynomial (Fin 4) ℂ

def h : R := X 0
def u : R := X 1
def v : R := X 2
def w : R := X 3

def x : R := u ^ 3 + h * v
def y : R := -u ^ 2 + h * w
def s : R := 2 * u ^ 3 * v + 3 * u ^ 4 * w + h * (v ^ 2 - 3 * u ^ 2 * w ^ 2) + h ^ 2 * w ^ 3

/-- p(x,y,s) = -2 s^2 x + 3 s y^2 - 3 s^3 y -/
def p (x y s : R) : R := -2 * s ^ 2 * x + 3 * s * y ^ 2 - 3 * s ^ 3 * y

def F : R := h - p x y s - 1

/-- "Coordinate": F is the first component of a polynomial automorphism of 𝔸^n, i.e. some
ℂ-algebra automorphism σ of the coordinate ring sends the first variable to F. -/
def IsCoordinate {n : ℕ} (hn : 0 < n) (f : MvPolynomial (Fin n) ℂ) : Prop :=
  ∃ σ : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ, σ (X ⟨0, hn⟩) = f

theorem reading_thm_quotient :
    Nonempty ((R ⧸ Ideal.span {F}) ≃ₐ[ℂ] MvPolynomial (Fin 3) ℂ) := sorry

theorem reading_thm_gradient :
    ∀ i : Fin 4, eval (![2, 0, -1/2, 1/2] : Fin 4 → ℂ) (pderiv i F) = 0 := sorry

theorem reading_thm_noncoordinate : ¬ IsCoordinate (by norm_num : 0 < 4) F := sorry

theorem reading_cor :
    ∀ (n : ℕ) (hn : 4 ≤ n), ∃ f : MvPolynomial (Fin n) ℂ,
      Nonempty ((MvPolynomial (Fin n) ℂ ⧸ Ideal.span {f}) ≃ₐ[ℂ] MvPolynomial (Fin (n - 1)) ℂ) ∧
      ¬ IsCoordinate (by omega : 0 < n) f := sorry

/-
AMBIGUITIES AND CHOICES
- Variable order: Fin 4 with h=0, u=1, v=2, w=3 (order of "R = C[h,u,v,w]").
- x, y, s, p, F typed verbatim from (eq:xyz)-(eq:F); F = h - p(x,y,s) - 1.
- C^[m] = MvPolynomial (Fin m) C; isomorphism is a C-algebra equiv (AlgEquiv), per "fix C".
  Stated as Nonempty (existence), since the source says "≅".
- Quotient R/(F) as Ideal.Quotient by Ideal.span {F}.
- Gradient: all four partial derivatives (pderiv i) evaluated at the point (2,0,-1/2,1/2)
  in the same variable order (h=2,u=0,v=-1/2,w=1/2); numerals in ℂ.
- "Coordinate": source says "first component of a polynomial automorphism of A^n". I formalize
  as existence of a C-algebra automorphism σ of the polynomial ring with σ(z_1) = f
  (the comorphism of an automorphism of A^n has first component f iff σ(z_1) = f). "First" = index 0.
  Needs a proof 0 < n for Fin n index; passed as argument.
- Theorem says "Consequently F is not a coordinate"; stated as ¬IsCoordinate for n=4.
- Corollary: n : ℕ with 4 ≤ n; n - 1 is natural subtraction, harmless since n ≥ 4 (so = n-1 truly).
  Statement is ∃ f in n variables with quotient ≅ C^[n-1] and f not coordinate.
-/

end ReadingB
end
end ReaderB

namespace ReaderC

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
end ReaderC
