import Mathlib

/-! Blind readings A, B, C (code unchanged; only `import Mathlib` hoisted). -/

-- ===== reader A =====

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

-- ===== reader B =====

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

-- ===== reader C =====

namespace ReaderC

/-! Reading of O33: Theorem 1.1 and Corollary 1.2.

Variables: p, s, u, F, J are the indices 0, 1, 2, 3, 4 of `MvPolynomial (Fin 5) ℂ` (the ring P).
Definitions written from the source:
* x = s^2 + u^3 + p^2 F
* H = x^2 F - (1 + 2 s x) J - p^2 J^2 - p u
* A = P / (H)   (the ideal generated by H in P)
* A[w] is `Polynomial A` (adjoining one independent variable w), an ℂ-algebra.
* "Polynomial ring in r variables" is `MvPolynomial (Fin r) ℂ`.
* Isomorphisms are ℂ-algebra isomorphisms (`≃ₐ[ℂ]`).
* "Integral" = `IsDomain`; "dimension four" = `ringKrullDim A = 4`.

Corollary 1.2 choices:
* "Coordinate": a polynomial f ∈ k[y_0..y_{n-1}] is a coordinate if some k-algebra
  automorphism of k[y_0..y_{n-1}] maps some variable `X i` to f. This is the source's notion
  of a polynomial coordinate (the conjecture concerns polynomial automorphisms of the
  ambient space); it is the usual definition, and does not force the variable index.
* The source writes the base field as `\kk`; the corollary is stated over an arbitrary field `k`
  (the theorem is then the case k = ℂ). The theorem is stated over ℂ as in the brief.
* P[w] is `MvPolynomial (Fin 6) k`, with H viewed in it via the renaming `Fin.castSucc`
  (the new variable w is index 5). This identifies P[w] as a polynomial ring in six variables.
-/

open MvPolynomial


noncomputable def xpoly {k : Type} [Field k] : MvPolynomial (Fin 5) k :=
  X 1 ^ 2 + X 2 ^ 3 + X 0 ^ 2 * X 3

noncomputable def Hpoly {k : Type} [Field k] : MvPolynomial (Fin 5) k :=
  xpoly ^ 2 * X 3 - (1 + 2 * X 1 * xpoly) * X 4 - X 0 ^ 2 * X 4 ^ 2 - X 0 * X 2

/-- The algebra A = P/(H). -/
noncomputable abbrev Aalg {k : Type} [Field k] := MvPolynomial (Fin 5) k ⧸ Ideal.span {Hpoly (k := k)}

/-- A polynomial f in n variables is a coordinate: some automorphism sends a variable to f. -/
def IsCoordinate {k : Type} [Field k] {n : ℕ} (f : MvPolynomial (Fin n) k) : Prop :=
  ∃ i : Fin n, ∃ σ : MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (Fin n) k, σ (X i) = f

/-- Theorem 1.1 over ℂ. -/
theorem reading_cancellation_thm11 :
    IsDomain (Aalg (k := ℂ)) ∧ ringKrullDim (Aalg (k := ℂ)) = 4 ∧
    Nonempty (Polynomial (Aalg (k := ℂ)) ≃ₐ[ℂ] MvPolynomial (Fin 5) ℂ) ∧
    IsEmpty (Aalg (k := ℂ) ≃ₐ[ℂ] MvPolynomial (Fin 4) ℂ) := by
  sorry

/-- Corollary 1.2: H is not a coordinate of P, but is a coordinate of P[w]. -/
theorem reading_cancellation_cor12 {k : Type} [Field k] :
    ¬ IsCoordinate (Hpoly (k := k)) ∧
    IsCoordinate (MvPolynomial.rename (Fin.castSucc : Fin 5 → Fin 6) (Hpoly (k := k))) := by
  sorry

end ReaderC
