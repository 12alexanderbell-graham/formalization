import Mathlib

/-!
Blind reading A of O33: Theorem 1.1 and Corollary 1.2 (failure of Zariski cancellation over ℂ in
dimension four; failure of the Stable Coordinate Conjecture in ambient dimension five).
-/

namespace ReaderA

open MvPolynomial

/-- `P = ℂ[p, s, u, F, J]`, variables indexed by `Fin 5` in this order. -/
abbrev P := MvPolynomial (Fin 5) ℂ

noncomputable def p : P := X 0
noncomputable def s : P := X 1
noncomputable def u : P := X 2
noncomputable def F : P := X 3
noncomputable def J : P := X 4

/-- `x = s² + u³ + p² F`. -/
noncomputable def x : P := s ^ 2 + u ^ 3 + p ^ 2 * F

/-- `H = x² F − (1 + 2 s x) J − p² J² − p u`. -/
noncomputable def H : P := x ^ 2 * F - (1 + 2 * s * x) * J - p ^ 2 * J ^ 2 - p * u

/-- `A = P / (H)`. -/
abbrev A := P ⧸ Ideal.span ({H} : Set P)

/-- Theorem 1.1, part 1: `A` is integral (an integral domain). -/
theorem reading_thm_1_1_integral : IsDomain A := sorry

/-- Theorem 1.1, part 2: `A` has (Krull) dimension four. -/
theorem reading_thm_1_1_dim : ringKrullDim A = 4 := sorry

/-- Theorem 1.1, part 3: `A[w] ≅ ℂ[5 variables]` as ℂ-algebras. -/
theorem reading_thm_1_1_cylinder :
    Nonempty (Polynomial A ≃ₐ[ℂ] MvPolynomial (Fin 5) ℂ) := sorry

/-- Theorem 1.1, part 4: `A ≇ ℂ[4 variables]` as ℂ-algebras. -/
theorem reading_thm_1_1_not_affine :
    ¬ Nonempty (A ≃ₐ[ℂ] MvPolynomial (Fin 4) ℂ) := sorry

/-- Theorem 1.1, all parts together. -/
theorem reading_thm_1_1 :
    IsDomain A ∧ ringKrullDim A = 4 ∧
      Nonempty (Polynomial A ≃ₐ[ℂ] MvPolynomial (Fin 5) ℂ) ∧
      ¬ Nonempty (A ≃ₐ[ℂ] MvPolynomial (Fin 4) ℂ) := sorry

/-- `f` is a coordinate (a variable) of the polynomial ring `ℂ[X_i : i ∈ σ]`: some ℂ-algebra
automorphism of the polynomial ring sends one of the variables to `f`, i.e. `f` is a member of a
system of polynomial coordinates. -/
def IsCoordinate {σ : Type*} (f : MvPolynomial σ ℂ) : Prop :=
  ∃ (e : MvPolynomial σ ℂ ≃ₐ[ℂ] MvPolynomial σ ℂ) (i : σ), e (X i) = f

/-- `P[w] = ℂ[p, s, u, F, J, w]`, with `w = X none`, and `P ↪ P[w]` via `X i ↦ X (some i)`. -/
noncomputable def toPw : P →ₐ[ℂ] MvPolynomial (Option (Fin 5)) ℂ := rename some

/-- Corollary 1.2: `H` is not a coordinate of `P`, but is a coordinate of `P[w]`. -/
theorem reading_cor_1_2 : ¬ IsCoordinate H ∧ IsCoordinate (toPw H) := sorry

end ReaderA

/-
AMBIGUITIES AND CHOICES

1. Variables. `p, s, u, F, J` are "algebraically independent over ℂ" and `P = ℂ[p,s,u,F,J]`:
   modelled as the five variables `X 0,…,X 4` of `MvPolynomial (Fin 5) ℂ`, in that order.
   `x` is an abbreviation (a definition), and `H` is the displayed polynomial verbatim.

2. "Integral complex algebra": read as "integral domain" (`IsDomain A`). The ℂ-algebra structure
   on `A = P ⧸ (H)` is Mathlib's quotient algebra structure; "finitely generated" is automatic.

3. "Dimension four": Krull dimension, `ringKrullDim A = 4` (in `WithBot ℕ∞`). For a finitely
   generated domain over a field this equals the transcendence degree / the dimension of Spec A.

4. `A[w]`: one independent variable adjoined, modelled as `Polynomial A` with the ℂ-algebra
   structure induced from `A`. `ℂ^[n]` is `MvPolynomial (Fin n) ℂ`. Isomorphisms are ℂ-algebra
   isomorphisms (`≃ₐ[ℂ]`), matching "all isomorphisms fix the complex scalars". The negation
   `A ≇ ℂ^[4]` is `¬ Nonempty (A ≃ₐ[ℂ] …)`.

5. "Coordinate": the source says the Stable Coordinate Conjecture "concerns polynomial
   automorphisms of the ambient spaces", so I define `f ∈ ℂ[X_σ]` to be a coordinate iff there is a
   ℂ-algebra automorphism of `ℂ[X_σ]` sending some variable `X i` to `f` (equivalently, `f` can be
   completed to a system of variables `f, f₂, …, fₙ` with `ℂ[X_σ] = ℂ[f, f₂, …, fₙ]`).
   The residual/stable coordinate notions over `ℂ[p]` in the "polynomial cylinder" paragraph are
   proof remarks; not formalized.

6. `P[w]`: modelled as `MvPolynomial (Option (Fin 5)) ℂ` with `w = X none`, and `H` transported via
   `rename some` (the standard inclusion `P ⊆ P[w]`). "Not a coordinate of P" is stated in `P`
   itself (`MvPolynomial (Fin 5) ℂ`).

7. The "Consequently …"/"Thus the Stable Coordinate Conjecture fails" sentences are corollaries of
   the stated facts and not stated separately.

8. No junk values: no division or partial functions are used; all objects are honest polynomial
   rings and quotients.
-/
