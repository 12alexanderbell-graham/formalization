import Mathlib

namespace ReaderB

open MvPolynomial

/-- Evaluate `P ∈ ℤ[A₁..Aₙ, W₁..W_m]` at `a` and `w` (naturals cast to ℤ). -/
def evalAW {n m : ℕ} (P : MvPolynomial (Fin n ⊕ Fin m) ℤ) (a : Fin n → ℕ) (w : Fin m → ℕ) : ℤ :=
  MvPolynomial.eval (Sum.elim (fun i => (a i : ℤ)) (fun j => (w j : ℤ))) P

/-- Theorem 1.1: r.e. sets have single-fold Diophantine representations. -/
theorem reading_singlefold_main (n : ℕ) (hn : 1 ≤ n) (S : Set (Fin n → ℕ))
    (hS : REPred (fun a : Fin n → ℕ => a ∈ S)) :
    ∃ (m : ℕ) (_ : 1 ≤ m) (P : MvPolynomial (Fin n ⊕ Fin m) ℤ), ∀ a : Fin n → ℕ,
      (a ∈ S → ∃! w : Fin m → ℕ, evalAW P a w = 0) ∧
      (a ∉ S → ∀ w : Fin m → ℕ, evalAW P a w ≠ 0) := sorry

/-- A polynomial in `ℤ[W₁..W_m]` given as a finite list of (exponent vector, coefficient) terms. -/
noncomputable def polyOfTerms {m : ℕ} (L : List ((Fin m → ℕ) × ℤ)) : MvPolynomial (Fin m) ℤ :=
  (L.map fun t => MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm t.1) t.2).sum

/-- Corollary: with a promise of at most one solution, no algorithm decides solvability. -/
theorem reading_singlefold_cor :
    ∃ (m D : ℕ), 1 ≤ m ∧ 1 ≤ D ∧
      ¬ ∃ f : List ((Fin m → ℕ) × ℤ) → Bool, Computable f ∧
        ∀ L : List ((Fin m → ℕ) × ℤ),
          (polyOfTerms L).totalDegree ≤ D →
          {w : Fin m → ℕ | MvPolynomial.eval (fun i => (w i : ℤ)) (polyOfTerms L) = 0}.Subsingleton →
          (f L = true ↔ ∃ w : Fin m → ℕ, MvPolynomial.eval (fun i => (w i : ℤ)) (polyOfTerms L) = 0) := sorry

/-
Ambiguities / choices:
* r.e.: Mathlib `REPred` (partial-recursive semi-decidable) on `Fin n → ℕ`, which is `Primcodable`; this is
  closest to "a deterministic computation accepts exactly its members, may run forever otherwise".
* "exactly one w with P(a,w)=0": stated as ∃! for a ∈ S and no solution otherwise, rather than
  Set.ncard = 1/0, because ncard of an infinite set is the junk value 0. Equivalent to the source count.
* ℕ = {0,1,..} (Lean ℕ); variables evaluated by casting to ℤ; polynomial ring MvPolynomial (Fin n ⊕ Fin m) ℤ.
  m ≥ 1 included as existential witness.
* Corollary: Mathlib has no Primcodable on MvPolynomial, so inputs are encoded as a list of
  (exponent vector, integer coefficient) terms (Primcodable), polynomial = sum of monomials;
  degree promise is on the resulting polynomial's totalDegree ≤ D, solution promise is Set.Subsingleton
  (≤ 1, avoiding ncard). The "algorithm" is a `Computable` Bool-valued function, total, as the source
  says the algorithm halts on every promise input (it may behave arbitrarily elsewhere; here f is total
  and merely unconstrained off-promise, which is the weakest reading). Zero-term list is the zero polynomial.
  "There exist m, D ≥ 1" is stated existentially. Encoding choice (term lists) is a modelling assumption.
-/
end ReaderB
