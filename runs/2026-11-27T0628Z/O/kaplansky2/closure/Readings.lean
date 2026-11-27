import Mathlib

namespace ReaderA

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
end ReaderA

namespace ReaderB

/-- Theorem 1.1 (stated as proved in the source). `Group.IsFinitelyPresented` and
`MonoidAlgebra K G` from Mathlib are used. "Odd prime order" = `orderOf g` prime and `≠ 2`. -/
theorem reading :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2)
      (G : Type) (_ : Group G),
      Group.IsFinitelyPresented G ∧
      (∃ g : G, Nat.Prime (orderOf g) ∧ orderOf g ≠ 2) ∧
      ∃ a b : MonoidAlgebra K G, a * b = 1 ∧ b * a ≠ 1 := sorry

/-- The cellular automaton on `A^G` with memory set `M` and local rule `φ`:
`τ(x)(g) = φ((x(g u))_{u ∈ M})`. -/
def cellularAutomaton {G : Type} [Group G] {A : Type} (M : Finset G)
    (φ : (M → A) → A) (x : G → A) : G → A :=
  fun g => φ (fun u : M => x (g * (u : G)))

/-- Gottschalk consequence (negative resolution of Gottschalk's conjecture for the group of
Thm 1.1): some such group `G` (finitely presented, with an element of odd prime order) is not
surjunctive, i.e. there are a finite alphabet `A`, finite memory set `M ⊆ G` and local rule `φ`
with the cellular automaton injective but not surjective. -/
theorem reading_gottschalk :
    ∃ (G : Type) (_ : Group G),
      Group.IsFinitelyPresented G ∧
      (∃ g : G, Nat.Prime (orderOf g) ∧ orderOf g ≠ 2) ∧
      ∃ (A : Type) (_ : Finite A) (M : Finset G) (φ : (M → A) → A),
        Function.Injective (cellularAutomaton M φ) ∧
        ¬ Function.Surjective (cellularAutomaton M φ) := sorry

/-
AMBIGUITIES / CHOICES
* Claims: Theorem 1.1 is stated as proved ("We ... obtain"; "Thus Theorem resolves ... negatively").
  The Gottschalk statement is a consequence ("Section cellular proves this standard transfer in
  full ... gives a negative resolution of Gottschalk's conjecture for the group in Theorem"),
  stated as proved too (derived from the theorem, not an independent main theorem).
* Source lines 45-52 start mid-definition: the lines defining A, M, phi are missing. I assumed
  A finite set (the source says "finite-alphabet", "finite-set implication"), M ⊆ G finite
  ("finite local dependence"), phi : A^M -> A. Group may be nontrivially infinite; A^G = G → A.
* Convention: tau(x)(g) = phi((x(gu))_{u in M}) with right multiplication g*u, as written.
* "Surjunctive: every injective CA on A^G is surjective, for every such A": so a group is
  non-surjunctive iff exists finite A, M, phi, injective and not surjective. I state this for
  the specific group of Thm 1.1, existentially (the source's group is not named/fixed here, so
  I existentially re-quantify; I do not tie it to the same K, a, b — a stronger reading would
  give A = K, M = supports, but the source excerpt does not say that).
* A could be required nonempty; non-surjective+injective forces it automatically (empty A with
  G nonempty gives no maps... fine).
* "odd prime order": orderOf g prime, ≠ 2. orderOf = 0 (infinite order) is not prime, so no junk.
* Finite field of char 2: Field K, Fintype K, CharP K 2 (not necessarily ZMod 2; source says
  K ≠ F_2 not asserted). Types in universe 0 for existential quantification.
* Multiplication in MonoidAlgebra K G: Mathlib's convolution (a*b)(g)=∑_{xy=g} a x b y, matching
  "multiplied using the group law".
* a_out, b_out names dropped; `1 : MonoidAlgebra K G` is single 1 1.
-/
end ReaderB

namespace ReaderC

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
end ReaderC
