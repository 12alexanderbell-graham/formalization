import Mathlib

namespace ReaderB

open Computability

/-- Characteristic function of a set of integers, as a (total) partial function ℕ →. ℕ. -/
noncomputable def charFn (A : Set ℕ) : ℕ →. ℕ := fun n => by classical exact Part.some (if n ∈ A then 1 else 0)

/-- Sets of integers, as a type synonym so that we may give it the Turing preorder
without clashing with the inclusion order on `Set ℕ`. -/
def IntSet : Type := Set ℕ

/-- `A ≤T B`: an oracle machine with oracle `B` computes the characteristic function of `A`
(Mathlib's `TuringReducible` for partial functions, applied to the characteristic functions). -/
def leT (A B : IntSet) : Prop := charFn A ≤ᵀ charFn B

instance : Preorder IntSet where
  le := leT
  le_refl A := TuringReducible.refl _
  le_trans _ _ _ := TuringReducible.trans

/-- The Turing degrees: classes of mutually reducible sets of integers, with the induced order. -/
abbrev Degrees : Type := Antisymmetrization IntSet (· ≤ ·)

/-- Theorem 1.1: every order automorphism (bijection π with a ≤ b ↔ π a ≤ π b, no regularity
assumption) of the Turing degrees is the identity. -/
theorem readingRigidity (π : Degrees → Degrees) (hπ : Function.Bijective π)
    (hord : ∀ a b : Degrees, a ≤ b ↔ π a ≤ π b) : ∀ a : Degrees, π a = a := sorry

end ReaderB

/-
Ambiguities and choices.
* Degrees of sets vs. partial functions: the text speaks of sets of integers with oracle machines
  computing the characteristic function. Mathlib's `TuringDegree` is built from partial functions
  ℕ →. ℕ; I did not use it, and instead took degrees of sets via characteristic functions
  (total, valued in {0,1}) and Mathlib's `TuringReducible` (recursive-in) on those. Degrees of
  total functions/sets are the same poset as the usual degrees; the poset of degrees of all partial
  functions is a different (larger) structure, so this choice matters and follows the text.
* Order: `Antisymmetrization` of the preorder gives the quotient partial order; `≤` on it is the
  induced `≤ᵀ`. The type synonym `IntSet` avoids using the inclusion order on `Set ℕ`.
* Automorphism: stated literally as a bijective map with a ≤ b ↔ π a ≤ π b, rather than `≃o`,
  to follow the text (an `≃o` would be equivalent).
* No ℕ subtraction, division, sSup/sInf, or ⊤ occurs; nothing junk-valued.
-/
/- Decidability of `n ∈ A` in `charFn` is supplied classically (`open Classical`); the function is
   still the genuine characteristic function. -/
