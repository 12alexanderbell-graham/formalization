import Mathlib

/-!
Blind reading of family O3 ("A Counterexample to Kaplansky's Direct-Finiteness Conjecture in
Characteristic Two"), reader C.
Sources: `kaplansky2/sources/01-introduction_lines1-20.tex` (Theorem 1.1 and its context) and
`kaplansky2/sources/01-introduction_lines45-52.tex` (cellular-automaton definitions).
-/

/-- Theorem 1.1 (source `thm:main`): there exist a finite field `K` of characteristic two, a
finitely presented group `G` containing an element of odd prime order, and `a, b ∈ K[G]` with
`a * b = 1` and `b * a ≠ 1`.

Choices:
* `K[G]` is Mathlib's `MonoidAlgebra K G`, with product from the group law and `1 = single 1 1`.
* "finite field of characteristic two": `Field K`, `Finite K`, `CharP K 2`.
* "finitely presented group": `Group.IsFinitelyPresented G`.
* "element of odd prime order": `∃ g : G, ∃ p : ℕ, p.Prime ∧ Odd p ∧ orderOf g = p`.
  (`orderOf` is `0` for infinite order, so the `Prime` clause already excludes it.)
* The source states this as a theorem; the intro says its termination and product assertions
  are proved (certificates), not computed. -/
theorem reading :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (G : Type) (_ : Group G),
      Group.IsFinitelyPresented G ∧
      (∃ g : G, ∃ p : ℕ, p.Prime ∧ Odd p ∧ orderOf g = p) ∧
      ∃ a b : MonoidAlgebra K G, a * b = 1 ∧ b * a ≠ 1 := sorry

/-- Cellular automaton on the configuration space `A^G = G → A` with a finite memory set `M ⊆ G`
and a local rule `φ : (M → A) → A`, following lines 45–52 of the source:
`τ(x)(g) = φ((x(g u))_{u ∈ M})`, with `g * u` the group product. -/
def cellularAutomaton {A G : Type} [Group G] (M : Finset G) (φ : ({u // u ∈ M} → A) → A) :
    (G → A) → (G → A) :=
  fun x g => φ (fun u => x (g * u.1))

/-- Surjunctivity, from lines 45–52 of the source: `G` is surjunctive if every injective
cellular automaton on `A^G` is surjective, for every finite alphabet `A`. Quantified over all
finite memory sets `M` and all local rules `φ` on them. -/
def IsSurjunctive (G : Type) [Group G] : Prop :=
  ∀ (A : Type) [Finite A] (M : Finset G) (φ : ({u // u ∈ M} → A) → A),
    Function.Injective (cellularAutomaton M φ) → Function.Surjective (cellularAutomaton M φ)

/-- Gottschalk's consequence for the group of Theorem 1.1 (source lines1–20, line 7: "a negative
resolution of Gottschalk's conjecture for the group in Theorem"). Stated as the existence of
`K, G, a, b` as in `reading`, together with `¬ IsSurjunctive G`. The same `G` is used in both
conjuncts. -/
theorem reading_gottschalk :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (G : Type) (_ : Group G),
      Group.IsFinitelyPresented G ∧
      (∃ g : G, ∃ p : ℕ, p.Prime ∧ Odd p ∧ orderOf g = p) ∧
      (∃ a b : MonoidAlgebra K G, a * b = 1 ∧ b * a ≠ 1) ∧
      ¬ IsSurjunctive G := sorry

/-!
## Ambiguities and choices (reader C)

1. "Finite field of characteristic two": `K` is `Type`, `[Field K] [Finite K] [CharP K 2]`.
   The source says K is not necessarily F_2 ("does not assert that K = F_2"), so the statement
   is existential in `K`. I did not fix a particular field.
2. "Finitely presented group": Mathlib's `Group.IsFinitelyPresented`. "Containing an element of
   odd prime order": `∃ g, ∃ p, p.Prime ∧ Odd p ∧ orderOf g = p`. I used `Odd p` rather than
   `p ≠ 2`; these agree for primes.
3. Algebra: `MonoidAlgebra K G` (finite formal sums with group-law product). `1` is the identity
   of the algebra. The source says "elements of K[G]" and "finite formal sums", which is this
   object.
4. Stated as a theorem vs consequence: `reading` (Theorem 1.1) is stated as a theorem in the
   source. `reading_gottschalk` is a consequence. The source says (line 7) that it "gives a
   negative resolution of Gottschalk's conjecture for the group in Theorem" and that Section
   (cellular) "proves this standard transfer in full"; the transfer is not in my excerpts, so I
   took the consequence as stated in the intro.
5. Cellular automata (Mathlib has none). Source lines 45–52 give only the tail of the
   definition: `τ(x)(g) = φ((x(gu))_{u∈M})`. The head of that definition (the finite memory
   set `M`, the local rule `φ`, the alphabet `A`) is not in my excerpt, so I supplied the
   natural reading: `M : Finset G` finite, `φ : (M → A) → A`, `A` finite. Configurations are
   `G → A` (all functions, not finite support). I used `{u // u ∈ M}` for the subtype of `M`.
   Note: `M` may be empty. Then `φ` is constant, and the injectivity hypothesis is never
   satisfied when `G` is nontrivial. This is harmless for the statement, which is about the
   universal property.
6. Multiplication convention: I used `g * u` (group product with `g` on the left), as the source writes `x(gu)`. The source says the multiplication convention is handled in its cellular section, which is not in my excerpt. I did not check whether `u * g` would change the statement, so this choice is recorded, not verified.
7. `IsSurjunctive` is quantified over `A : Type` with `[Finite A]`. The source says "for every
   such A" where "such" is the finite alphabet. No universe issue arises in our `Type` setting.
8. `reading_gottschalk` gives `¬ IsSurjunctive G` (the source's "negative resolution"), which by definition means some finite alphabet, memory set and rule give an injective but not surjective automaton. The source does not name that alphabet, so I did not identify it with `K`.
9. `sorry` only in `reading` and `reading_gottschalk`; the CA and surjunctivity definitions are
   complete (no sorry in definitions).
-/
