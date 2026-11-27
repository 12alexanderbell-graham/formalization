import Mathlib

namespace ReaderB

open MvPolynomial

/-- Variables of `P = ℂ[p,s,u,F,J]` indexed by `Fin 5`. -/
abbrev P := MvPolynomial (Fin 5) ℂ

noncomputable def p : P := X 0
noncomputable def s : P := X 1
noncomputable def u : P := X 2
noncomputable def F : P := X 3
noncomputable def J : P := X 4

noncomputable def x : P := s ^ 2 + u ^ 3 + p ^ 2 * F

noncomputable def H : P := x ^ 2 * F - (1 + 2 * s * x) * J - p ^ 2 * J ^ 2 - p * u

/-- `A = P/(H)`. -/
abbrev A := P ⧸ Ideal.span {H}

/-- `f` is a coordinate of the polynomial ring `ℂ[σ]` if some ℂ-algebra automorphism of the
polynomial ring sends one of the variables to `f` (equivalently, `f` is part of a system of
polynomial generators). -/
def IsCoordinate {σ : Type} (f : MvPolynomial σ ℂ) : Prop :=
  ∃ (e : MvPolynomial σ ℂ ≃ₐ[ℂ] MvPolynomial σ ℂ) (i : σ), e (X i) = f

theorem reading_cancellation_main :
    IsDomain A ∧ ringKrullDim A = 4 ∧
      Nonempty (Polynomial A ≃ₐ[ℂ] MvPolynomial (Fin 5) ℂ) ∧
      ¬ Nonempty (A ≃ₐ[ℂ] MvPolynomial (Fin 4) ℂ) := sorry

/-- `P[w]` is `MvPolynomial (Option (Fin 5)) ℂ`, with `w = X none`, and `P ⊆ P[w]` via
`rename some`. -/
theorem reading_cancellation_coordinate :
    ¬ IsCoordinate H ∧ IsCoordinate (rename (some : Fin 5 → Option (Fin 5)) H) := sorry

end ReaderB

/-
Ambiguities and choices.
* The base field kk is ℂ. Variables p,s,u,F,J are X 0..X 4 of MvPolynomial (Fin 5) ℂ; they are
  algebraically independent by construction. Numerals 1, 2 are ℂ-constants.
* "Integral" = IsDomain A (integral domain), "integral complex algebra" read as integral domain, not
  "integral extension". Dimension four = ringKrullDim A = 4 (Krull dimension, values in WithBot ℕ∞).
* "A[w] ≃ ℂ[5 variables]": Polynomial A (one indeterminate over A) ≃ₐ[ℂ] MvPolynomial (Fin 5) ℂ, as
  ℂ-algebras (the algebra structure on Polynomial A over ℂ is Mathlib's canonical one).
  "A ≄ ℂ[4 variables]": no ℂ-algebra equivalence (¬ Nonempty).
* Coordinate (source: "polynomial automorphisms of the ambient spaces", Stable Coordinate Conjecture):
  f ∈ ℂ[σ] is a coordinate iff some ℂ-algebra automorphism of ℂ[σ] sends some variable X i to f.
  Equivalent to f being a member of a polynomial generating system.
* "coordinate of P[w]": P[w] modelled as MvPolynomial (Option (Fin 5)) ℂ (w = X none), H embedded by
  `rename some`. This is a 6-variable ring (source says ambient dimension five after stabilization,
  i.e. five original variables plus w; the source's own ambiguous phrasing, I use P[w] literally).
* Junk values avoided: none needed; ringKrullDim equality is in WithBot ℕ∞ so no truncation.
-/
