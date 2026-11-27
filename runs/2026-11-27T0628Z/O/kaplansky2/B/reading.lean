import Mathlib

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
