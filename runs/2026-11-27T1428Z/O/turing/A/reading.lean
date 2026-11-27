import Mathlib

/-!
Blind reading A of O53, "Rigidity of the Turing degrees", Theorem 1.1.
-/

namespace ReaderA

/-- The characteristic function of a set of natural numbers, as a (total) partial function
`ℕ →. ℕ` (value `1` on members, `0` on non-members). -/
noncomputable def chi (A : Set ℕ) : ℕ →. ℕ :=
  open Classical in fun n => Part.some (if n ∈ A then 1 else 0)

/-- `A ≤T B`: the characteristic function of `A` is computable relative to the oracle `B`
(i.e. to the characteristic function of `B`), using Mathlib's oracle computability
`TuringReducible` (= `RecursiveIn {chi B} (chi A)`). -/
def LeT (A B : Set ℕ) : Prop := TuringReducible (chi A) (chi B)

theorem LeT.refl (A : Set ℕ) : LeT A A := TuringReducible.refl _

theorem LeT.trans {A B C : Set ℕ} (h₁ : LeT A B) (h₂ : LeT B C) : LeT A C :=
  TuringReducible.trans h₁ h₂

/-- Turing equivalence: mutual reducibility. -/
def TEquiv (A B : Set ℕ) : Prop := LeT A B ∧ LeT B A

/-- Turing equivalence as a setoid on sets of naturals. -/
def turingSetoid : Setoid (Set ℕ) where
  r := TEquiv
  iseqv :=
    { refl := fun A => ⟨LeT.refl A, LeT.refl A⟩
      symm := fun h => ⟨h.2, h.1⟩
      trans := fun h₁ h₂ => ⟨LeT.trans h₁.1 h₂.1, LeT.trans h₂.2 h₁.2⟩ }

/-- `𝒟_T`, the set of Turing degrees: equivalence classes of sets of naturals under
Turing equivalence. -/
def DT : Type := Quotient turingSetoid

/-- The induced order `𝐚 ≤T 𝐛` on Turing degrees. -/
def DT.le : DT → DT → Prop :=
  Quotient.lift₂ (s₁ := turingSetoid) (s₂ := turingSetoid) LeT
    (fun _ _ _ _ hA hB =>
      propext ⟨fun h => LeT.trans hA.2 (LeT.trans h hB.1),
               fun h => LeT.trans hA.1 (LeT.trans h hB.2)⟩)

/-- Theorem 1.1. Every order automorphism of `(𝒟_T, ≤T)` — any bijection `π` with
`𝐚 ≤T 𝐛 ↔ π 𝐚 ≤T π 𝐛`, no definability hypothesis — is the identity. -/
theorem reading_rigidity :
    ∀ π : DT → DT, Function.Bijective π →
      (∀ a b : DT, DT.le a b ↔ DT.le (π a) (π b)) →
      ∀ a : DT, π a = a := sorry

end ReaderA

/-!
Ambiguities and choices.

1. "Sets of integers": read, as is standard in computability theory, as sets of natural
   numbers `Set ℕ` (not `Set ℤ`). Since ℤ is computably isomorphic to ℕ the degree structure
   would be the same.
2. "Oracle Turing machine with oracle B computes the characteristic function of A": rendered
   with Mathlib's `TuringReducible` (`RecursiveIn {g} f`: `f` is in the closure of the basic
   partial recursive functions plus the oracle `g` under composition, pairing, primitive
   recursion and unbounded search). This is Mathlib's model of oracle computation; it is
   classically equivalent to oracle Turing machines. Characteristic functions are encoded as
   total `ℕ →. ℕ` with values 0/1, using classical decidability of membership (no
   computability of `A` itself is assumed — `chi` is merely a function).
3. Mathlib's own `TuringDegree` is the quotient of *partial functions* `ℕ →. ℕ`, a different
   (larger) structure than degrees of sets; I did not use it, and instead built `𝒟_T` as the
   quotient of `Set ℕ` by mutual reducibility, matching the source.
4. "Automorphism" is taken exactly as the text defines it: any bijection `π : 𝒟_T → 𝒟_T` with
   `a ≤ b ↔ π a ≤ π b` (an order embedding which is bijective = order isomorphism). Stated
   with an explicit bijectivity hypothesis instead of `DT ≃o DT` to stay literal. No
   definability/measurability is required of `π`; Lean's ambient logic (with Classical) plays
   the role of ZFC.
5. Junk values: none arise — no subtraction, division, sup/inf or extended values are used.
-/
