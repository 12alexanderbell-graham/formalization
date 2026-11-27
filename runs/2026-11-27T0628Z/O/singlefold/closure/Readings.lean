import Mathlib

/-! Blind readings A, B, C (code unchanged; only `import Mathlib` hoisted). -/

-- ===== reader A =====

namespace ReaderA

open MvPolynomial

/-- Evaluation of `P ∈ ℤ[A₁,…,Aₙ,W₁,…,W_m]` at `(a, w) ∈ ℕⁿ × ℕ^m`. The variables are indexed
by `Fin n ⊕ Fin m`: `Sum.inl i` is `A_{i+1}` and `Sum.inr j` is `W_{j+1}`. -/
noncomputable def evalAW {n m : ℕ} (P : MvPolynomial (Fin n ⊕ Fin m) ℤ)
    (a : Fin n → ℕ) (w : Fin m → ℕ) : ℤ :=
  eval (Sum.elim (fun i => (a i : ℤ)) (fun j => (w j : ℤ))) P

/-- The witness set `{w ∈ ℕ^m : P(a, w) = 0}`. -/
def witnesses {n m : ℕ} (P : MvPolynomial (Fin n ⊕ Fin m) ℤ) (a : Fin n → ℕ) :
    Set (Fin m → ℕ) :=
  {w | evalAW P a w = 0}

/-- Theorem 1.1: for every `n ≥ 1` and every recursively enumerable `S ⊆ ℕⁿ` there are
`m ≥ 1` and `P ∈ ℤ[A₁,…,Aₙ,W₁,…,W_m]` such that for every `a ∈ ℕⁿ`,
`#{w ∈ ℕ^m : P(a,w) = 0}` is `1` if `a ∈ S` and `0` if `a ∉ S`.
The count is `Set.encard` (an infinite set has `encard = ⊤`, not a junk `0`). -/
theorem reading_thm_1_1 (n : ℕ) (hn : 1 ≤ n) (S : Set (Fin n → ℕ))
    (hS : REPred (fun a => a ∈ S)) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ P : MvPolynomial (Fin n ⊕ Fin m) ℤ,
      ∀ a : Fin n → ℕ,
        (a ∈ S → (witnesses P a).encard = 1) ∧ (a ∉ S → (witnesses P a).encard = 0) := by
  sorry

/-- Concrete input format for an algorithm receiving a polynomial `F ∈ ℤ[W₁,…,W_m]`: a finite
list of terms `(e, c)`, where `c ∈ ℤ` is a coefficient and the list `e` of naturals gives the
exponents of `W₁, W₂, …` (missing entries are `0`, extra entries are ignored). -/
noncomputable def decodePoly (m : ℕ) (L : List (List ℕ × ℤ)) : MvPolynomial (Fin m) ℤ :=
  (L.map fun t => C t.2 * ∏ i : Fin m, X i ^ (t.1.getD (i : ℕ) 0)).sum

/-- Evaluation of `F ∈ ℤ[W₁,…,W_m]` at `w ∈ ℕ^m`. -/
noncomputable def evalW {m : ℕ} (F : MvPolynomial (Fin m) ℤ) (w : Fin m → ℕ) : ℤ :=
  eval (fun j => (w j : ℤ)) F

/-- Corollary (undecidability with an at-most-one-solution promise): there are integers
`m, D ≥ 1` such that no algorithm (partial recursive function on encoded polynomials) halts
and correctly decides `∃ w ∈ ℕ^m, F(w) = 0` on every input `F ∈ ℤ[W₁,…,W_m]` of total degree
`≤ D` satisfying the promise `#{w ∈ ℕ^m : F(w) = 0} ≤ 1`. -/
theorem reading_corollary :
    ∃ m D : ℕ, 1 ≤ m ∧ 1 ≤ D ∧
      ¬ ∃ f : List (List ℕ × ℤ) →. Bool, Partrec f ∧
        ∀ L : List (List ℕ × ℤ),
          (decodePoly m L).totalDegree ≤ D →
          {w : Fin m → ℕ | evalW (decodePoly m L) w = 0}.encard ≤ 1 →
          ∃ b ∈ f L, (b = true ↔ ∃ w : Fin m → ℕ, evalW (decodePoly m L) w = 0) := by
  sorry

end ReaderA

/-
Ambiguities and choices.

1. ℕ = {0,1,2,…} (source says so): Lean's ℕ. ℕⁿ is `Fin n → ℕ`; ℕ^m is `Fin m → ℕ`.
2. "recursively enumerable" ("a deterministic computation accepts exactly its members; it may
   run forever on other inputs"): Mathlib's `REPred` (Mathlib/Computability/RE.lean), i.e. the
   membership predicate is the domain of a partial recursive (`Partrec`) function on the
   `Primcodable` type `Fin n → ℕ` (instance `Primcodable.finArrow`). This is exactly
   "halts (accepts) iff member, may diverge otherwise", which is why I chose it over
   `ComputablePred` (decidable, too strong) or an ad hoc Turing-machine model. Mathlib's
   `Partrec` is equivalent to Turing-machine computability (Mathlib's Turing machine
   equivalence files), so the choice of model does not matter.
3. ℤ[A₁…Aₙ, W₁…W_m]: `MvPolynomial (Fin n ⊕ Fin m) ℤ`, with the A's evaluated at a and the W's
   at w, both cast ℕ → ℤ. "P(a,w) = 0" is evaluation in ℤ.
4. "#{w ∈ ℕ^m : P(a,w) = 0} = 1 / 0": `Set.encard` (values in ℕ∞), so an infinite witness set
   cannot be counted as 0 (the junk value of `Set.ncard`). `encard = 1` means exactly one
   complete tuple w; `encard = 0` means none. The source's two-case display is written as
   (a ∈ S → … = 1) ∧ (a ∉ S → … = 0), avoiding a classical `if` on the undecidable `a ∈ S`. m ≥ 1 and n ≥ 1 are kept as hypotheses /
   conclusions as stated. P is not required to depend on all variables (as in the source).
5. Corollary, "algorithm" on "input polynomial F": Mathlib has no `Primcodable` instance on
   `MvPolynomial`, so inputs are given as finite lists of (exponent list, ℤ coefficient)
   terms, decoded by `decodePoly`; every F ∈ ℤ[W₁…W_m] has such a representation. An
   algorithm is a `Partrec` function `List (List ℕ × ℤ) →. Bool` (ℤ is Primcodable via its
   `Denumerable` instance). "Halts and correctly decides" = `∃ b ∈ f L` (the computation
   terminates with value b) and `b = true ↔ the witness set is nonempty`. Requiring
   correctness on every representation L of a promised F is equivalent to requiring it on
   every F (an algorithm on polynomials gives one on representations by decoding first;
   correctness pins down the answer from F alone). Total degree is Mathlib's
   `MvPolynomial.totalDegree` of the decoded polynomial (so representations with cancelling
   terms are judged by the actual polynomial, as the source's "F of total degree ≤ D").
6. Promise "#{…} ≤ 1": again `Set.encard ≤ 1`, so infinite witness sets violate the promise.
7. "There exist integers m, D ≥ 1": ∃ m D : ℕ with 1 ≤ m, 1 ≤ D, quantified before the
   algorithm (one fixed (m, D) defeats all algorithms).
-/

-- ===== reader B =====

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

-- ===== reader C =====

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
