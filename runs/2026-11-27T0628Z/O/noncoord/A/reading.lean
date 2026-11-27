import Mathlib

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
