import Mathlib

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
