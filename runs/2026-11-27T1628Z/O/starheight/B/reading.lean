import Mathlib

namespace ReaderB

/-- Generalized regular expressions over an alphabet `α`: 0, 1, letters, union,
concatenation, complement, star. -/
inductive GRE (α : Type) : Type
  | zero : GRE α
  | one : GRE α
  | letter : α → GRE α
  | union : GRE α → GRE α → GRE α
  | concat : GRE α → GRE α → GRE α
  | compl : GRE α → GRE α
  | star : GRE α → GRE α

namespace GRE
variable {α : Type}

/-- Denotation; complement is taken in `α*` (all of `Language α`). -/
def sem : GRE α → Language α
  | zero => 0
  | one => 1
  | letter a => {[a]}
  | union P Q => sem P + sem Q
  | concat P Q => sem P * sem Q
  | compl P => (sem P)ᶜ
  | star P => KStar.kstar (sem P)

/-- Generalized star height, exactly the recursion of the text. -/
def sht : GRE α → ℕ
  | zero => 0
  | one => 0
  | letter _ => 0
  | union P Q => max (sht P) (sht Q)
  | concat P Q => max (sht P) (sht Q)
  | compl P => sht P
  | star P => 1 + sht P

end GRE

/-- Regular: accepted by a DFA with a finite state type. -/
def IsRegularLang {α : Type} (L : Language α) : Prop :=
  ∃ (σ : Type) (_ : Fintype σ) (M : DFA α σ), M.accepts = L

/-- `h_Σ(L) ≤ n` : some expression defining `L` has height `≤ n`
(avoids a least-element operator). -/
def HasHeightAtMost {α : Type} (L : Language α) (n : ℕ) : Prop :=
  ∃ e : GRE α, e.sem = L ∧ e.sht ≤ n

/-- Theorem 1.1: every regular language over every finite alphabet has generalized
star height at most three. -/
theorem readingThm1_1 (α : Type) [Fintype α] (L : Language α) (hL : IsRegularLang L) :
    HasHeightAtMost L 3 := sorry

/-
Ambiguities and choices.
* "Regular": existence of a DFA over a finite state type accepting L (equivalent to NFA,
  regex, Myhill-Nerode finiteness). Alphabet and states are in `Type` (universe 0); finite
  alphabet via `[Fintype α]`.
* h_Σ(L) is "least height of an expression defining L". To avoid sInf/Nat.find I state
  existence of an expression of height ≤ 3, which is equivalent to h_Σ(L) ≤ 3 for the
  least height (which exists for regular L anyway).
* Letters are `letter a` denoting {[a]}; 0 is ∅ (`0 : Language`), 1 is {[]} (`1`); union is `+`
  on Language, concat `*`, star is `KStar.kstar`, complement is `ᶜ` in the full `List α`.
* The text says Σ is fixed and finite; empty alphabet is allowed (then Σ* = {ε}); no junk values
  are used: no subtraction, division, sInf, etc. ℕ addition and max only.
-/

end ReaderB
