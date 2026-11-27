import Mathlib

/-! # Target O, family starheight: the three blind readings of run 2026-11-27T1628Z (brief da5a1fc), concatenated unchanged
apart from the repeated `import Mathlib` lines, so a closure can import them as one module. -/


/-!
Blind reading A of O59, "Generalized star height at most three", Theorem 1.1.
Source: abstract + introduction lines 1-41.
-/

namespace ReaderA

/-- Generalized regular expressions over the alphabet `α`: `0`, `1`, singleton letters,
union, concatenation, complement, Kleene star (introduction, lines 16-19). -/
inductive GRE (α : Type*) where
  | zero : GRE α
  | one : GRE α
  | letter : α → GRE α
  | union : GRE α → GRE α → GRE α
  | concat : GRE α → GRE α → GRE α
  | compl : GRE α → GRE α
  | star : GRE α → GRE α

namespace GRE

variable {α : Type*}

/-- The language denoted by an expression. `0 ↦ ∅`, `1 ↦ {ε}`, `a ↦ {a}`, union, concatenation
`{uv}`, complement taken in `Σ*` (= all of `List α`), and Kleene star (with `ε ∈ P*`).
We use Mathlib's `Language α = Set (List α)` operations: `0`, `1`, `+` (union),
`*` (concatenation), `∗` (Kleene star), `ᶜ` (Boolean complement in `Set (List α)`). -/
def denote : GRE α → Language α
  | zero => 0
  | one => 1
  | letter a => ({[a]} : Set (List α))
  | union P Q => denote P + denote Q
  | concat P Q => denote P * denote Q
  | compl P => (denote P)ᶜ
  | star P => KStar.kstar (denote P)

/-- The (generalized) star height, exactly as in the displayed recursion (lines 21-28). -/
def sht : GRE α → ℕ
  | zero => 0
  | one => 0
  | letter _ => 0
  | union P Q => max (sht P) (sht Q)
  | concat P Q => max (sht P) (sht Q)
  | compl P => sht P
  | star P => 1 + sht P

end GRE

/-- `h_Σ(L) ≤ k`, phrased without taking a least element: some expression defining `L`
has height at most `k`. (Since heights are natural numbers, "the least height is ≤ k" is
equivalent to this whenever some expression defines `L`.) -/
def HeightAtMost {α : Type*} (L : Language α) (k : ℕ) : Prop :=
  ∃ e : GRE α, e.denote = L ∧ e.sht ≤ k

/-- Theorem 1.1. For every finite alphabet `Σ` and every regular language `L ⊆ Σ*`,
`h_Σ(L) ≤ 3`. "Regular" = Mathlib's `Language.IsRegular` (accepted by a DFA with finitely
many states). The alphabet is an arbitrary type with a `Fintype` instance (possibly empty);
universe-polymorphic in the alphabet. -/
theorem reading_thm_1_1 {α : Type*} [Fintype α] (L : Language α) (hL : L.IsRegular) :
    HeightAtMost L 3 := sorry

end ReaderA

/-
AMBIGUITIES AND CHOICES

1. "Regular" (lines 29, 36): the text does not define it. Chosen: Mathlib's
   `Language.IsRegular` = accepted by a DFA with a finite (`Fintype`) state type. This is
   the standard notion (equivalent to NFA / ordinary regular expressions / finite monoid
   recognition). The theorem is only stated for regular `L`; we do not claim anything for
   non-regular `L` (note GRE languages are all regular anyway, so the hypothesis is the
   natural one).

2. "Finite alphabet Σ": an arbitrary type `α` with `[Fintype α]`. No `DecidableEq` needed.
   The empty alphabet is included (the text says "every finite alphabet"). Universe: `α`
   is universe-polymorphic (`Type*`).

3. Semantics: `0 ↦ ∅`, `1 ↦ {ε}` (lines 18-19), letter `a ↦ {[a]}`, union, concatenation,
   complement in `Σ*` = `List α` (Mathlib's `ᶜ` on `Language α = Set (List α)`, which is
   exactly complement in Σ*), Kleene star including ε (Mathlib's `∗`, standard;
   the text does not say otherwise).

4. Height: exactly the recursion in lines 21-28. Note `sht (P*) = 1 + sht P` written
   as `1 + sht P` (no subtraction anywhere).

5. `h_Σ(L)` is "the least height of an expression defining L". To avoid `sInf`/`Nat.find`
   on a possibly empty set, the claim `h_Σ(L) ≤ 3` is stated as "there is an expression
   denoting L whose height is ≤ 3". For a nonempty set of naturals, "least element ≤ 3"
   iff "some element ≤ 3", so this is equivalent and also asserts that some expression
   defines `L` (which is implicit in the text, as `h_Σ(L)` must exist).

6. Lines 43-46 (expressions use the letters of Σ itself; parameters may depend on L; no
   size bound) are reflected by: the expression is over the same alphabet `α`, existential
   per `L`, with no size bound.

7. "with complement taken in the same free monoid" (abstract): ensured since `denote`
   always lands in `Language α` over the same `α`; no extended alphabet.

Junk values: none used. No ℕ subtraction, no division, no sInf/iInf, no Nat.find.
-/


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
