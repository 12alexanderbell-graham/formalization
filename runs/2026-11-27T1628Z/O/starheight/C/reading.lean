import Mathlib

/-!
Reader C, family O59: generalized star height at most three.

Definitions are written from the text (abstract and introduction, lines 1-41).
Lean reserves the token `Σ`, so the alphabet is written `α` below.

Ambiguities and choices:
* Alphabet: `α : Type` with `[Fintype α]` (finite alphabet). Words are `List α`, and
  `α*` is the set of all lists, so complement is `Set.univ \ P` inside `Set (List α)`.
* "Regular": a language is regular when it is recognized by a deterministic finite
  automaton, given here as a finite state type `Q`, a transition `δ : Q → α → Q`,
  a start state `q0` and an accepting set `F`. The run on `w` is `List.foldl δ q0 w`.
* Generalized regular expressions form an inductive type with constructors for
  `0`, `1`, letters, union, concatenation, complement and star. Their denotation is
  given by `lang`, with complement taken in `α*` (that is, `Set.univ`).
* Star: the text's `P^*` is the set of finite concatenations of words of `P`,
  including the empty concatenation. We encode it as
  `∃ l : List (List α), (∀ u ∈ l, u ∈ P) ∧ l.flatten = w`.
* Height `ht` is exactly the text's `sht`: `ht 0 = ht 1 = ht a = 0`,
  `ht (P ∪ Q) = ht (PQ) = max`, `ht (¬P) = ht P`, `ht (P^*) = 1 + ht P`.
  Natural-number `max` and `+` are used, so there is no subtraction or junk value.
* `h_α(L)` is the least height of an expression defining `L`. Stating it with `sInf`
  would introduce a junk value `0` on the empty set. The theorem below instead says
  that some expression of height at most three defines `L`. This is equivalent to
  `h_α(L) ≤ 3`, since a least element exists whenever the set is nonempty.
  If no expression exists, the statement is false, so it is not vacuous.
-/

namespace ReaderC

/-- Generalized regular expressions over an alphabet `α`. -/
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

/-- Generalized star height `sht` from the text. -/
def ht : GRE α → ℕ
  | zero => 0
  | one => 0
  | letter _ => 0
  | union P Q => max (ht P) (ht Q)
  | concat P Q => max (ht P) (ht Q)
  | compl P => ht P
  | star P => 1 + ht P

/-- Language denoted by an expression; complement is taken in `α*` (all lists). -/
def lang : GRE α → Set (List α)
  | zero => ∅
  | one => {[]}
  | letter a => {[a]}
  | union P Q => lang P ∪ lang Q
  | concat P Q => {w | ∃ u v, w = u ++ v ∧ u ∈ lang P ∧ v ∈ lang Q}
  | compl P => Set.univ \ lang P
  | star P => {w | ∃ l : List (List α), (∀ u ∈ l, u ∈ lang P) ∧ l.flatten = w}

end GRE

/-- A language `L ⊆ α*` is regular when some finite deterministic automaton accepts exactly `L`. -/
def IsRegularLang {α : Type} (L : Set (List α)) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (δ : Q → α → Q) (q0 : Q) (F : Set Q),
    L = {w : List α | List.foldl δ q0 w ∈ F}

/-- Reading of Theorem 1.1: every regular language over every finite alphabet is defined by
a generalized regular expression of height at most three. -/
theorem reading_starheight_le_three :
    ∀ (α : Type) [Fintype α] (L : Set (List α)), IsRegularLang L →
      ∃ e : GRE α, GRE.lang e = L ∧ GRE.ht e ≤ 3 := by
  sorry

end ReaderC
