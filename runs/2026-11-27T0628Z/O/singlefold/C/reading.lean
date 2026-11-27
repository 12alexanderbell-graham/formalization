import Mathlib

namespace ReaderC

open MvPolynomial

/-- Evaluation of P ∈ ℤ[A_1..A_n, W_1..W_m] (variables indexed by `Fin n ⊕ Fin m`)
at (a, w) ∈ ℕⁿ × ℕᵐ, with the natural-number values cast into ℤ. -/
noncomputable def evalAW {n m : ℕ} (P : MvPolynomial (Fin n ⊕ Fin m) ℤ)
    (a : Fin n → ℕ) (w : Fin m → ℕ) : ℤ :=
  MvPolynomial.eval (Sum.elim (fun i => (a i : ℤ)) (fun j => (w j : ℤ))) P

/-- Theorem 1.1 (single-fold representation over ℕ). Recursive enumerability is Mathlib's
`REPred` (domain of a partial recursive function, on the Primcodable type `Fin n → ℕ`).
For each a, the number of w ∈ ℕᵐ with P(a, w) = 0 is `Set.encard` (ℕ∞-valued), which
is 1 exactly when a ∈ S and 0 otherwise. -/
theorem reading_singlefold_main (n : ℕ) (hn : 1 ≤ n) (S : Set (Fin n → ℕ))
    (hS : REPred (fun a : Fin n → ℕ => a ∈ S)) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ P : MvPolynomial (Fin n ⊕ Fin m) ℤ, ∀ a : Fin n → ℕ,
      (a ∈ S → Set.encard {w : Fin m → ℕ | evalAW P a w = 0} = 1) ∧
      (a ∉ S → Set.encard {w : Fin m → ℕ | evalAW P a w = 0} = 0) := sorry

/-- Corollary (undecidability with an at-most-one-solution promise).
Inputs are polynomials F ∈ ℤ[W_1..W_m] given as finite lists of terms
(exponent list, coefficient); `polyOfList` is the polynomial they denote.
There are m, D ≥ 1 such that no partial recursive g (Mathlib's `Partrec`) satisfies:
on every input with total degree ≤ D and at most one zero in ℕᵐ, g halts and its output
b satisfies b = true iff F has a zero in ℕᵐ. -/
noncomputable def polyOfList {m : ℕ} (L : List (List ℕ × ℤ)) : MvPolynomial (Fin m) ℤ :=
  (L.map fun t => MvPolynomial.monomial
    (Finsupp.equivFunOnFinite.symm fun i : Fin m => t.1.getD (i : ℕ) 0) t.2).sum

theorem reading_singlefold_corollary :
    ∃ m D : ℕ, 1 ≤ m ∧ 1 ≤ D ∧
      ¬ ∃ g : List (List ℕ × ℤ) →. Bool, Partrec g ∧
        ∀ L : List (List ℕ × ℤ),
          (polyOfList (m := m) L).totalDegree ≤ D →
          Set.encard {w : Fin m → ℕ |
              MvPolynomial.eval (fun j => (w j : ℤ)) (polyOfList (m := m) L) = 0} ≤ 1 →
          ∃ b : Bool, b ∈ g L ∧
            (b = true ↔ ∃ w : Fin m → ℕ,
              MvPolynomial.eval (fun j => (w j : ℤ)) (polyOfList (m := m) L) = 0) := sorry

/-
Ambiguities and choices (reader C):

1. Recursive enumerability: the text says "a deterministic computation accepts exactly its
   members; it may run forever on other inputs". I used Mathlib's `REPred`, defined as the
   domain of a `Partrec` function with the semi-decision Part.assert, which is the
   closest match. Its Primcodable structure on `Fin n → ℕ` is Mathlib's standard encoding.
2. Witnesses and parameters are ℕ-valued (ℕ = {0,1,2,…} as in the text). Coefficients and
   polynomial values are in ℤ; a ∈ ℕⁿ and w ∈ ℕᵐ are cast into ℤ in `evalAW`.
3. Variables: the polynomial lives in `MvPolynomial (Fin n ⊕ Fin m) ℤ`, where `inl i` is A_{i+1}
   and `inr j` is W_{j+1}. The text's m ≥ 1 is the condition `1 ≤ m`.
4. Exactly one solution: the count is `Set.encard` of {w ∈ ℕᵐ | P(a,w)=0} in ℕ∞, so an infinite
   solution set is ⊤ and fails both conjuncts (no junk 0 from ncard of infinite sets).
   The two implications (a ∈ S → count 1) and (a ∉ S → count 0) are kept separate to avoid
   needing decidability of membership in S.
5. "Finite-fold"/"single-fold" definitions in the text count all auxiliary variables; this is
   built in because the count is over complete tuples w ∈ ℕᵐ.
6. The Theorem's hn : 1 ≤ n is given as in the text (n ≥ 1). It is not used in the statement
   beyond being a hypothesis.
7. Corollary: "algorithm" is a partial recursive function (Partrec) from codes of polynomials
   to Bool. A polynomial F ∈ ℤ[W] of total degree ≤ D is encoded by `polyOfList`: a finite
   list of (exponent list, coefficient) terms; exponent entries beyond index m are ignored
   and repeated exponents add. Every polynomial with the required form is denoted by some
   list, so the encoding covers all inputs. Total degree is Mathlib's `totalDegree`.
8. "Halts and correctly decides": formalized as ∃ b ∈ g L (g L is a Part, so membership
   means halting with output b), with b = true iff F has a zero in ℕᵐ. The promise
   "#{w ∈ ℕᵐ : F(w)=0} ≤ 1" is `Set.encard ≤ 1` (ℕ∞-valued, so infinite sets violate it).
   Note the algorithm is only required to be correct on promised inputs; it may do anything
   on others, which the statement allows because the promise is a hypothesis of the implication.
9. The corollary's quantifier is ¬ ∃ g, so the m, D are chosen by the theorem and no
   algorithm exists for them. I used the existential ∃ m D rather than fixing values.
-/

end ReaderC
