import Mathlib

/-!
# Blind reading A, family O3: "A Counterexample to Kaplansky's Direct-Finiteness Conjecture in
Characteristic Two"

Source: 01-introduction.tex, lines 1--20 (Theorem 1.1 = thm:main) and lines 45--52
(cellular automata, surjunctivity, Gottschalk consequence).

Mathlib objects used:
* `MonoidAlgebra K G` -- the group algebra `K[G]` (finitely supported `G → K`, multiplication
  `single g c * single h d = single (g * h) (c * d)`, i.e. "multiplied using the group law").
* `Group.IsFinitelyPresented G` -- Mathlib's class (finitely many generators `Fin n`, kernel
  finitely normally generated).
* `orderOf`, `Nat.Prime`, `Odd`, `CharP`, `Finite`, `Field`.
Mathlib has no cellular automata / surjunctivity, so these are defined below from line 45--47.
-/

namespace BlindReadingA.Kaplansky

/-- Theorem 1.1 (thm:main), as literally as possible: there exist a finite field `K` of
characteristic two, a finitely presented group `G` containing an element of odd prime order, and
elements `a_out, b_out ∈ K[G]` with `a_out * b_out = 1` and `b_out * a_out ≠ 1`. -/
theorem reading :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (G : Type) (_ : Group G) (_ : Group.IsFinitelyPresented G),
      (∃ (g : G) (p : ℕ), p.Prime ∧ Odd p ∧ orderOf g = p) ∧
      ∃ a_out b_out : MonoidAlgebra K G, a_out * b_out = 1 ∧ b_out * a_out ≠ 1 := sorry

/-- A cellular automaton on `A^G` (source line 45): a map `τ : A^G → A^G` for which there are a
finite memory set `M ⊆ G` and a local rule `φ : A^M → A` with
`τ(x)(g) = φ((x(g u))_{u ∈ M})` for all configurations `x` and all `g ∈ G`. -/
def IsCellularAutomaton {G A : Type} [Group G] (τ : (G → A) → (G → A)) : Prop :=
  ∃ (M : Finset G) (φ : (M → A) → A), ∀ (x : G → A) (g : G), τ x g = φ (fun u => x (g * u))

/-- `G` is surjunctive (source line 47): for every finite alphabet `A`, every injective cellular
automaton on `A^G` is surjective. -/
def Surjunctive (G : Type) [Group G] : Prop :=
  ∀ (A : Type) [Finite A] (τ : (G → A) → (G → A)),
    IsCellularAutomaton τ → Function.Injective τ → Function.Surjective τ

/-- Gottschalk's conjecture (source line 47): every group is surjunctive. -/
def GottschalkConjecture : Prop := ∀ (G : Type) [Group G], Surjunctive G

/-- Cellular-automaton consequence (source lines 51--52): "a negative resolution of Gottschalk's
conjecture for the group in Theorem 1.1". Since Theorem 1.1 is existential, "the group in
Theorem 1.1" is read as: some group witnessing Theorem 1.1 (together with its field and its pair
`a_out, b_out`) is not surjunctive. -/
theorem reading_gottschalk :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (G : Type) (_ : Group G) (_ : Group.IsFinitelyPresented G),
      (∃ (g : G) (p : ℕ), p.Prime ∧ Odd p ∧ orderOf g = p) ∧
      (∃ a_out b_out : MonoidAlgebra K G, a_out * b_out = 1 ∧ b_out * a_out ≠ 1) ∧
      ¬ Surjunctive G := sorry

/-- Immediate corollary of `reading_gottschalk` (stated, not proved): Gottschalk's conjecture,
as defined above, is false. -/
theorem reading_gottschalk_conjecture_false : ¬ GottschalkConjecture := sorry

end BlindReadingA.Kaplansky

/-!
## Ambiguities and choices (reader A)

Theorem 1.1
1. "finite field K of characteristic two": `Field K`, `Finite K`, `CharP K 2`. Not `K = ZMod 2`;
   the source explicitly says it does not assert `K = F_2` (line 18).
2. "finitely presented group": Mathlib's `Group.IsFinitelyPresented` (exists; used).
3. "containing an element of odd prime order": `∃ g p, p.Prime ∧ Odd p ∧ orderOf g = p`.
   Junk check: `orderOf g = 0` for elements of infinite order, but `0` is not prime, so the
   clause cannot be satisfied vacuously. `Odd p` with `p` prime is the same as `p ≠ 2`.
4. "K[G]" and "1": `MonoidAlgebra K G` with its ring structure; `1 = single 1 1`. The source's
   multiplication convention ("multiplied using the group law") is Mathlib's convolution
   `single g c * single h d = single (g*h) (c*d)`. Its direct-finiteness question is about
   `ab = 1 → ba = 1`; we state the negation with names `a_out, b_out` exactly as in the source.
   Note `ab = 1, ba ≠ 1` and the opposite order are equivalent up to swapping names, so no
   left/right ambiguity affects the statement.
5. Universes: `K` and `G` quantified in `Type` (universe 0). An existential in `Type 0` is the
   strongest/most natural reading.
6. Line 15, "The field, group, and finite sums are specified by a terminating prescription
   involving finite sets and finite-field arithmetic": an effectivity/constructivity claim. Not
   formalized (a classical `∃` in Lean does not express it); flagged as omitted.
7. Line 18, "resolves the unrestricted conjecture negatively in characteristic two": a direct
   consequence of Theorem 1.1, not separately stated.

Cellular automata (lines 45--52)
8. Line 45 is the tail of the CA definition (`τ(x)(g) = φ((x(gu))_{u∈M})`); the preceding lines
   introducing `A`, `M`, `φ` are not in the sources. Choices: `M` a finite subset of `G`
   (`Finset G`), `φ : A^M → A` an arbitrary function, configurations `G → A`, right
   multiplication `g * u` exactly as written (this makes τ commute with the left shift action).
9. "for every such A": the qualifier "such" refers to text not shown; I read it as "every finite
   alphabet" (`A : Type`, `[Finite A]`), the standard setting of Gottschalk's conjecture.
   Empty `A` is harmless: `G → A` is then empty (groups are nonempty) and every self-map of it
   is bijective, so allowing it neither weakens nor strengthens surjunctivity.
10. Injective/surjective: `Function.Injective`/`Function.Surjective` on `(G → A) → (G → A)`.
11. "the group in Theorem 1.1": Theorem 1.1 is existential, so I bundle the Theorem 1.1
    properties and `¬ Surjunctive G` into one existential. A stronger reading suggested by
    lines 49--51 (the alphabet can be taken to be `K` itself, with a `K`-linear CA built from the
    coefficients of `b_out`, with left inverse from `a_out`) is NOT stated; only non-
    surjunctivity is.

Proved vs consequence (per the source)
12. Theorem 1.1 is stated as proved: it is the paper's main theorem (line 6, "Our construction
    ... to obtain"; line 18, "its termination is proved, and the two product assertions have
    algebraic certificates"). The prescription "has not been executed" (line 18): the witnesses
    are not exhibited concretely.
13. The Gottschalk failure for the group of Theorem 1.1 is a consequence of Theorem 1.1 via the
    standard algebra-to-automaton transfer, which the source says Section (sec:cellular) "proves
    in full" (line 51). So it is a proved corollary, not an independent result. The general
    Elek--Szabo / Ceccherini-Silberstein--Coornaert / Phung results (line 49) are cited, not proved.
14. `reading_gottschalk_conjecture_false` is my one-line logical consequence, not a separate
    claim of the source.
-/
