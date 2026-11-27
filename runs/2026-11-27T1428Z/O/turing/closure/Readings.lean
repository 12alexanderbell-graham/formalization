import Mathlib

/-! # Target O, family turing: the three blind readings of run 2026-11-27T1428Z (brief 35bb25e), concatenated unchanged
apart from the repeated `import Mathlib` lines, so a closure can import them as one module. -/


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


namespace ReaderC

open Classical in
/-- Characteristic function of a set of integers, as a total partial function `ℕ →. ℕ`. -/
noncomputable def chi (A : Set ℕ) : ℕ →. ℕ :=
  fun n => Part.some (if n ∈ A then 1 else 0)

/-- `A ≤T B`: the characteristic function of `A` is partial recursive relative to the oracle
`χ_B` (Mathlib's `TuringReducible`, i.e. `RecursiveIn {χ_B} χ_A`). -/
def leT (A B : Set ℕ) : Prop :=
  TuringReducible (chi A) (chi B)

theorem leT_refl (A : Set ℕ) : leT A A :=
  TuringReducible.refl _

theorem leT_trans {A B C : Set ℕ} (h₁ : leT A B) (h₂ : leT B C) : leT A C :=
  TuringReducible.trans h₁ h₂

/-- Turing equivalence `A ≡T B` as the kernel of the preorder `≤T`. -/
instance tSetoid : Setoid (Set ℕ) where
  r A B := leT A B ∧ leT B A
  iseqv :=
    ⟨fun A => ⟨leT_refl A, leT_refl A⟩,
     fun h => ⟨h.2, h.1⟩,
     fun h₁ h₂ => ⟨leT_trans h₁.1 h₂.1, leT_trans h₂.2 h₁.2⟩⟩

/-- The Turing degrees `\DT`: equivalence classes of sets of integers under `≡T`. -/
def DT : Type := Quotient tSetoid

/-- The degree of a set. -/
def deg (A : Set ℕ) : DT := Quotient.mk tSetoid A

/-- The partial order on degrees: `a ≤ b` iff some representatives satisfy `A ≤T B`.
This is independent of the representatives, since `≤T` is a preorder. -/
def leDeg (a b : DT) : Prop :=
  ∃ A B : Set ℕ, a = deg A ∧ b = deg B ∧ leT A B

/-- Theorem 1.1 (rigidity of the Turing degrees): every bijection `π` of `\DT` that preserves
and reflects `≤T` fixes every degree. -/
theorem reading_turing_rigidity :
    ∀ π : DT → DT, Function.Bijective π →
      (∀ a b : DT, leDeg a b ↔ leDeg (π a) (π b)) →
      ∀ a : DT, π a = a := by
  sorry

end ReaderC

/-!
## Comment block: ambiguities and choices (reader C, family O53 / Turing)

1. Turing reducibility. The text defines `A ≤T B` by an oracle Turing machine with oracle `B`
   computing the characteristic function of `A`. I did not write a machine model. I used
   Mathlib's own notion of relative computability, `TuringReducible f g = RecursiveIn {g} f`
   (partial recursive in the oracle `g`), applied to the characteristic functions `χ_A`, `χ_B`.
   These are total: `χ_A n = 1` if `n ∈ A`, else `0`. The two notions are classically
   equivalent; this is a modelling choice.
2. Classical decidability. Membership `n ∈ A` for an arbitrary `Set ℕ` is not decidable, so
   `chi` uses `open Classical`. This is only used to define the characteristic function; `chi`
   is therefore `noncomputable`.
3. The degrees. `\DT` is the quotient of `Set ℕ` by mutual `≤T`. I built the setoid from
   Mathlib's `TuringReducible.refl` and `TuringReducible.trans`, so no proof is left as `sorry`.
   I did not use Mathlib's `TuringDegree`, which is on partial functions `ℕ →. ℕ`, because the
   text is about sets of integers.
4. The order on `\DT`. `leDeg a b` holds iff there are representatives `A`, `B` of `a`, `b` with
   `A ≤T B`. Because `≤T` is a preorder, this is the well-defined induced order, and it is a
   partial order on the quotient (antisymmetry is built into the quotient). I chose the
   existential form over the universal form; the two agree here.
5. Automorphism. The text's automorphism is a bijection `π : \DT → \DT` with
   `a ≤ b ↔ π a ≤ π b`. I wrote exactly that: `Function.Bijective π` plus the iff. The
   conclusion `∀ a, π a = a` is the claim "every automorphism is the identity". The text's
   "full Turing-degree structure" is taken to be all of `\DT`, with no restriction.
6. No junk values. There is no ℕ subtraction, no division, no `sSup`/`sInf`, and no `⊤`.
7. Mathlib source read for names only: `Mathlib/Computability/TuringDegree.lean` (definitions
   `TuringReducible`, `TuringReducible.refl/trans`) and the `RecursiveIn` definitions in
   `Mathlib/Computability/RecursiveIn.lean`, plus a grep of the Computability directory for
   the word "oracle". No theorem bodies on rigidity were read.
-/
