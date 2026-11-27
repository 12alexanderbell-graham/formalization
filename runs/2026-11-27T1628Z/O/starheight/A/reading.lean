import Mathlib

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
