import Mathlib

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
