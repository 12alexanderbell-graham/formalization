import Mathlib

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
