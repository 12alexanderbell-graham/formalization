import Mathlib

/-! # Target O, family O66 (two-way automata): the three blind readings A, B, C, concatenated
unchanged (only their own `import Mathlib` lines removed), as module `Readings.automata`. -/


/-!
# Blind reading A of O66: exponential state costs for two-way automata

Paper 1, Theorem 1.1: for every `n` at least four, an `n`-state two-way nondeterministic
automaton recognizing the relation-product liveness language, whose complement needs
exponentially many states (in `n`) for any two-way nondeterministic automaton; and its
Corollary on determinization.
Paper 2, Theorem 1.1: one-way liveness on `h` points has a nondeterministic automaton with
`h + 3` states and no left moves, and every equivalent two-way deterministic automaton with
`s` states satisfies the stated exponential lower bound (with either acceptance convention, and
the sharper variant for the default convention); and its Corollary (no polynomial simulation).
The automaton model is written from the two model descriptions.
-/

open Relation

namespace ReaderA

/-! ## The automaton model -/

/-- Tape symbols: the two distinct endmarkers (outside the input alphabet) and input letters. -/
inductive TapeSym (α : Type) where
  | lend : TapeSym α
  | rend : TapeSym α
  | sym : α → TapeSym α

/-- Head moves: left, not at all, right. -/
inductive Dir where
  | left
  | stay
  | right

/-- A two-way (nondeterministic) finite automaton over input alphabet `α` with state set `Q`
(the state count is `Fintype.card Q`): one initial state, a set of accepting states, and a
transition relation depending only on the current state and the scanned symbol, giving
possible (new state, move) pairs. Missing transitions are allowed (empty successor sets). -/
structure TwoNFA (α : Type) (Q : Type) where
  init : Q
  acc : Set Q
  δ : Q → TapeSym α → Set (Q × Dir)

namespace TwoNFA

variable {α Q : Type}

/-- The symbol at position `i` of the tape `⊢ w ⊣` (positions `0 .. |w|+1`; position 0 is the
left endmarker, position `|w|+1` the right endmarker). -/
def tapeAt (w : List α) : ℕ → TapeSym α
  | 0 => TapeSym.lend
  | k + 1 => if h : k < w.length then TapeSym.sym (w.get ⟨k, h⟩) else TapeSym.rend

/-- One computation step on input `w` between configurations (state, head position). Moves
beyond either endmarker are impossible: a left move needs a position to the left, and a
right move must stay within position `|w|+1`. -/
def Step (M : TwoNFA α Q) (w : List α) : Q × ℕ → Q × ℕ → Prop
  | (q, i), (q', j) =>
      ∃ d : Dir, (q', d) ∈ M.δ q (tapeAt w i) ∧ j ≤ w.length + 1 ∧
        match d with
        | Dir.left => j + 1 = i
        | Dir.stay => j = i
        | Dir.right => j = i + 1

/-- Acceptance (default convention): some finite computation from the initial configuration
(initial state, head on the left endmarker) reaches an accepting state; an accepting initial
configuration counts (zero steps allowed). -/
def Accepts (M : TwoNFA α Q) (w : List α) : Prop :=
  ∃ c : Q × ℕ, ReflTransGen (M.Step w) (M.init, 0) c ∧ c.1 ∈ M.acc

/-- Acceptance (alternative convention of paper 2): success requires a positive number of
transitions, the last one entering an accepting state. -/
def AcceptsPos (M : TwoNFA α Q) (w : List α) : Prop :=
  ∃ c : Q × ℕ, TransGen (M.Step w) (M.init, 0) c ∧ c.1 ∈ M.acc

/-- The language recognized (default convention). -/
def lang (M : TwoNFA α Q) : Set (List α) := {w | M.Accepts w}

/-- The language recognized (positive-transition convention). -/
def langPos (M : TwoNFA α Q) : Set (List α) := {w | M.AcceptsPos w}

/-- Deterministic (2DFA): at most one successor for each state and scanned symbol. -/
def IsDet (M : TwoNFA α Q) : Prop := ∀ q a, (M.δ q a).Subsingleton

/-- No left moves. -/
def NoLeft (M : TwoNFA α Q) : Prop := ∀ q a q', (q', Dir.left) ∉ M.δ q a

end TwoNFA

/-! ## Relations and the liveness languages -/

/-- Binary relations on `H` (the alphabet `Σ_H = 𝓡_H`). -/
abbrev BRel (H : Type) := Set (H × H)

/-- Product in path order: `(p,r) ∈ AB ↔ ∃ q, (p,q) ∈ A ∧ (q,r) ∈ B`. -/
def relMul {H : Type} (A B : BRel H) : BRel H :=
  {x | ∃ q, (x.1, q) ∈ A ∧ (q, x.2) ∈ B}

/-- The identity relation `I_H = {(p,p)}`. -/
def relId (H : Type) : BRel H := {x | x.1 = x.2}

/-- The product `r(w) = R_1 ⋯ R_k` of a word, with `r(ε) = I_H`. (Computed as
`R_1 (R_2 (⋯ (R_k I_H)))`, equal to the left-to-right product by associativity.) -/
def wordProd {H : Type} : List (BRel H) → BRel H
  | [] => relId H
  | R :: w => relMul R (wordProd w)

/-- The relation-product liveness language `L_H = {w ∈ Σ_H^* : r(w) ≠ ∅}`. -/
def LH (H : Type) : Set (List (BRel H)) := {w | wordProd w ≠ ∅}

/-- `{1, …, m}` as a type. -/
abbrev Icc1 (m : ℕ) : Type := ↥(Finset.Icc 1 m)

/-- One-way liveness `OWL_h` on `[h] = {1, …, h}`. -/
def OWL (h : ℕ) : Set (List (BRel (Icc1 h))) := LH (Icc1 h)

/-! ## Paper 1 -/

/-- Paper 1, Theorem 1.1: for every integer `n ≥ 4`, with `H = {1,…,n-2}` and
`Σ_n = 𝓡_H`, there is an `n`-state 2NFA `A_n` recognizing `L_H` such that every 2NFA
recognizing `Σ_n^* \ L(A_n)` has at least `(1/2) 2^⌊(n-4)/127⌋ - 1` states. -/
theorem reading_paper1_theorem_1_1 :
    ∀ n : ℕ, 4 ≤ n →
      ∃ A : TwoNFA (BRel (Icc1 (n - 2))) (Fin n),
        A.lang = LH (Icc1 (n - 2)) ∧
        ∀ (Q : Type) [Fintype Q] (B : TwoNFA (BRel (Icc1 (n - 2))) Q),
          B.lang = A.langᶜ →
            (1 / 2 : ℝ) * 2 ^ ((n - 4) / 127) - 1 ≤ (Fintype.card Q : ℝ) := sorry

/-- Paper 1, Theorem 1.1, last sentence: there is no polynomial state bound for
complementation that is independent of the finite alphabet. -/
theorem reading_paper1_theorem_1_1_no_poly :
    ¬ ∃ p : Polynomial ℕ,
      ∀ (α : Type), Finite α → ∀ (n : ℕ) (A : TwoNFA α (Fin n)),
        ∃ (Q : Type) (_ : Fintype Q) (B : TwoNFA α Q),
          B.lang = A.langᶜ ∧ Fintype.card Q ≤ p.eval n := sorry

/-- Paper 1, Corollary (determinization): there are absolute constants `c > 0` and `n_0` such
that for every `n ≥ n_0`, every 2DFA recognizing the language of `A_n` (namely `L_H`,
`H = {1,…,n-2}`) has at least `c 2^⌊(n-4)/127⌋` states. -/
theorem reading_paper1_corollary :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, 4 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      ∀ (Q : Type) [Fintype Q] (D : TwoNFA (BRel (Icc1 (n - 2))) Q),
        D.IsDet → D.lang = LH (Icc1 (n - 2)) →
          c * 2 ^ ((n - 4) / 127) ≤ (Fintype.card Q : ℝ) := sorry

/-- Paper 1, Corollary, last sentence: no polynomial state bound independent of the finite
alphabet can determinize all 2NFAs. -/
theorem reading_paper1_corollary_no_poly :
    ¬ ∃ p : Polynomial ℕ,
      ∀ (α : Type), Finite α → ∀ (n : ℕ) (A : TwoNFA α (Fin n)),
        ∃ (Q : Type) (_ : Fintype Q) (D : TwoNFA α Q),
          D.IsDet ∧ D.lang = A.lang ∧ Fintype.card Q ≤ p.eval n := sorry

/-! ## Paper 2 -/

/-- Paper 2, Theorem 1.1. For every integer `h ≥ 2`:
(1) `OWL_h` is recognized by a nondeterministic automaton with `h + 3` states and no left moves;
(2) every equivalent deterministic two-way automaton with `s` states satisfies
`4 (s+2)^2 ≥ 2^⌊(h-2)/31⌋`, under the default acceptance convention and also under the
positive-transition convention ("holds with either convention");
(3) if an initially accepting configuration counts as acceptance (default convention), `s + 2`
may be replaced by `s + 1`. -/
theorem reading_paper2_theorem_1_1 :
    ∀ h : ℕ, 2 ≤ h →
      (∃ A : TwoNFA (BRel (Icc1 h)) (Fin (h + 3)), A.NoLeft ∧ A.lang = OWL h) ∧
      (∀ (Q : Type) [Fintype Q] (D : TwoNFA (BRel (Icc1 h)) Q),
        D.IsDet → D.lang = OWL h →
          2 ^ ((h - 2) / 31) ≤ 4 * (Fintype.card Q + 2) ^ 2) ∧
      (∀ (Q : Type) [Fintype Q] (D : TwoNFA (BRel (Icc1 h)) Q),
        D.IsDet → D.langPos = OWL h →
          2 ^ ((h - 2) / 31) ≤ 4 * (Fintype.card Q + 2) ^ 2) ∧
      (∀ (Q : Type) [Fintype Q] (D : TwoNFA (BRel (Icc1 h)) Q),
        D.IsDet → D.lang = OWL h →
          2 ^ ((h - 2) / 31) ≤ 4 * (Fintype.card Q + 1) ^ 2) := sorry

/-- Paper 2, Corollary: there are no absolute constants `C, c > 0` such that every `n`-state
two-way nondeterministic automaton over every finite alphabet has an equivalent two-way
deterministic automaton with at most `C n^c` states. -/
theorem reading_paper2_corollary :
    ¬ ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (α : Type), Finite α → ∀ (n : ℕ) (M : TwoNFA α (Fin n)),
        ∃ (Q : Type) (_ : Fintype Q) (D : TwoNFA α Q),
          D.IsDet ∧ D.lang = M.lang ∧ (Fintype.card Q : ℝ) ≤ C * (n : ℝ) ^ c := sorry

end ReaderA

/-
AMBIGUITIES AND CHOICES (reader A)

1. Automaton model (both papers describe the same model). States: a type `Q`, finite in every
   statement (`Fintype Q`, or `Fin n` for "n-state"); the state count is `Fintype.card Q`
   and counts all states including initial and accepting ones. One initial state `init`, a
   set `acc` of accepting states, transition relation `δ : Q → TapeSym α → Set (Q × Dir)`
   depending only on current state and scanned symbol. Partial rules = empty successor sets
   (missing transitions reject that branch). Moves: left, stay, right.
   Tape: `⊢ w ⊣` with two distinct endmarkers outside the alphabet (`TapeSym.lend`,
   `TapeSym.rend`), positions `0..|w|+1`; head starts at position 0 (left endmarker) in the
   initial state. No other resources.

2. "Forbid moves beyond either endmarker" / "the head cannot cross an endmarker": modelled
   semantically: a transition that would leave positions `0..|w|+1` simply cannot be taken
   (`Step` requires the target position to exist; `j + 1 = i` for left moves avoids ℕ
   subtraction). The alternative reading (such transitions must be absent from δ) gives the
   same languages with the same state sets (delete the offending transitions), so all state
   bounds are unaffected; for deterministic automata deleting transitions keeps determinism.

3. Acceptance: "some finite computation reaches an accepting state" = reachability under the
   reflexive-transitive closure of `Step` from `(init, 0)` to a configuration whose state is
   accepting. Zero steps are allowed (an accepting initial configuration counts, as both texts
   say for the default convention). Infinite nonaccepting computations simply never contribute
   (only finite reachability is used), so they reject. Acceptance does not require halting or
   being on an endmarker, as the text does not ask for that.
   Paper 2's alternative convention ("success requires a positive transition into an accepting
   state") is `AcceptsPos`, using `TransGen` (at least one step, the last step entering an
   accepting state).

4. Determinism: `(δ q a).Subsingleton`, i.e. at most one (state, move) successor per state and
   scanned symbol. "No left moves": no transition contains the move `left`.

5. Relations. `𝓡_H` = `Set (H × H)`; product in path order; `r(ε) = I_H`. `wordProd` folds from
   the right, `R_1 · (R_2 · (⋯ · I_H))`, which equals the left-to-right path-order product by
   associativity of relational composition. `L_H = {w | r(w) ≠ ∅}` and
   `OWL_h = L_{[h]}`. `H = {1,…,n-2}` and `[h] = {1,…,h}` are the literal subtypes
   `Finset.Icc 1 (n-2)`, `Finset.Icc 1 h` of ℕ. The alphabet `Set (H × H)` is finite since `H` is.

6. Paper 1 Theorem: "an n-state 2NFA A_n" = an automaton with state type `Fin n`.
   "Σ_n^* \ L(A_n)" = set complement `A.langᶜ` in `List Σ_n`. Bound
   `(1/2) 2^⌊(n-4)/127⌋ - 1` computed in ℝ (so the "- 1" is real subtraction, no truncation);
   the floor is ℕ division `(n - 4) / 127`, which with `n ≥ 4` has no truncated subtraction and
   is exactly the floor. Complement-recognizing 2NFAs: any finite state type, default acceptance.
   The "in particular" sentence is stated separately: no polynomial `p` (with ℕ coefficients;
   any real polynomial bound is dominated by one of these) such that every n-state 2NFA over
   every finite alphabet has a complement 2NFA with ≤ p(n) states.

7. Paper 1 Corollary: "the language of the n-state 2NFA A_n" is replaced by `L_H`, which equals
   `L(A_n)` by the theorem; so the corollary is stated for every 2DFA recognizing `L_H`, for every
   `n ≥ n₀`. I added `4 ≤ n₀` (harmless: `n₀` is existential and the statement for `n₀` implies
   it for any larger threshold; it avoids the meaningless `n < 4` cases where `n - 2` would be
   truncated). The bound `c 2^⌊(n-4)/127⌋` is real. The "Hence ..." sentence is stated
   separately as `reading_paper1_corollary_no_poly`.

8. Paper 2 Theorem. (1) The `h+3`-state automaton is a `TwoNFA` with state type `Fin (h+3)` and
   no left moves, recognizing `OWL_h` under the default acceptance convention (the text says it
   "initially" counts an accepting initial configuration as success; it does not say whether
   the upper bound is also claimed for the other convention, so I did not claim it).
   (2) "Every equivalent deterministic two-way automaton with s states" = every `IsDet`
   automaton with `Fintype.card Q = s` and the same language. Since the text says the main
   bound "holds with either convention", I state it for `lang` and for `langPos`.
   (3) The `s + 1` variant only for the default convention, as stated. All arithmetic is in ℕ:
   `(h - 2) / 31` with `h ≥ 2` is the exact floor; no subtraction elsewhere.

9. Paper 2 Corollary: "every n-state 2NFA over every finite alphabet has an equivalent 2DFA with
   at most C n^c states" is quantified over all `α : Type` with `Finite α`, all `n` and all
   `M : TwoNFA α (Fin n)`; equivalent = same language (default convention). `C n^c` uses
   `Real.rpow` with base `n ≥ 0` (never negative); `C, c > 0` real as stated.
   (The proof sketch's explicit bound is not part of the statement and is not formalized.)
-/


namespace ReaderB

/-- Head moves. -/
inductive Dir | L | S | R
  deriving DecidableEq

/-- Tape symbols: the two distinct endmarkers and the letters of `α`. -/
inductive Sym (α : Type) | lm | rm | ch (a : α)

/-- A two-way automaton (nondeterministic by default) on states `Q` over alphabet `α`.
The transition depends on the current state and scanned symbol; a missing transition is the empty set. -/
structure TwoWay (α Q : Type) where
  init : Q
  acc : Set Q
  trans : Q → Sym α → Set (Q × Dir)

/-- Deterministic: at most one successor per (state, scanned symbol) (rules may be partial). -/
def TwoWay.IsDet {α Q : Type} (A : TwoWay α Q) : Prop :=
  ∀ q s, (A.trans q s).Subsingleton

/-- No left moves. -/
def TwoWay.NoLeft {α Q : Type} (A : TwoWay α Q) : Prop :=
  ∀ q s, ∀ x ∈ A.trans q s, x.2 ≠ Dir.L

/-- The scanned symbol at head position `i` on the tape `⊢ w ⊣`, positions `0, …, |w|+1`. -/
def symAt {α : Type} (w : List α) : ℕ → Sym α
  | 0 => Sym.lm
  | j + 1 => if h : j < w.length then Sym.ch (w.get ⟨j, h⟩) else Sym.rm

/-- One computation step between configurations (state, head position). The head stays on the
tape (positions `0 … |w|+1`); a move beyond an endmarker is simply not available. -/
def TwoWay.Step {α Q : Type} (A : TwoWay α Q) (w : List α) (c c' : Q × ℕ) : Prop :=
  c.2 ≤ w.length + 1 ∧ c'.2 ≤ w.length + 1 ∧
    ∃ d, (c'.1, d) ∈ A.trans c.1 (symAt w c.2) ∧
      ((d = Dir.L ∧ c.2 = c'.2 + 1) ∨ (d = Dir.S ∧ c'.2 = c.2) ∨ (d = Dir.R ∧ c'.2 = c.2 + 1))

/-- Language, convention 1: an accepting initial configuration counts as acceptance
(a finite computation, possibly of length zero, reaches an accepting state). -/
def TwoWay.Lang {α Q : Type} (A : TwoWay α Q) : Set (List α) :=
  {w | ∃ q ∈ A.acc, ∃ i, Relation.ReflTransGen (A.Step w) (A.init, 0) (q, i)}

/-- Language, convention 2: acceptance requires at least one transition into an accepting state. -/
def TwoWay.LangPos {α Q : Type} (A : TwoWay α Q) : Set (List α) :=
  {w | ∃ q ∈ A.acc, ∃ i, Relation.TransGen (A.Step w) (A.init, 0) (q, i)}

/-- Binary relations on `H` as the alphabet `𝓡_H`. -/
abbrev Rel' (H : Type) := H → H → Prop

/-- Product of a word of relations in path order, `r(w) = R_1 ⋯ R_k`, with `r(ε) = Id`. -/
def relProd {H : Type} (w : List (Rel' H)) : Rel' H :=
  w.foldl (fun A R => Relation.Comp A R) Eq

/-- The liveness language `L_H = {w ∈ 𝓡_H^* : r(w) ≠ ∅}`. -/
def livenessLang (H : Type) : Set (List (Rel' H)) :=
  {w | ∃ a b, relProd w a b}

/-- An `s`-state (nondeterministic) automaton over `α` : the state type has `s` elements. -/
def HasStates {α Q : Type} [Fintype Q] (_A : TwoWay α Q) (s : ℕ) : Prop := Fintype.card Q = s

/-- Paper 1, Theorem 1.1. -/
theorem readingComplementation (n : ℕ) (hn : 4 ≤ n) :
    ∃ (Q : Type) (_ : Fintype Q) (A : TwoWay (Rel' (Fin (n - 2))) Q),
      Fintype.card Q = n ∧ A.Lang = livenessLang (Fin (n - 2)) ∧
      ∀ (Q' : Type) (_ : Fintype Q') (B : TwoWay (Rel' (Fin (n - 2))) Q'),
        B.Lang = {w | w ∉ A.Lang} →
        (1 / 2 : ℝ) * 2 ^ ((n - 4) / 127) - 1 ≤ (Fintype.card Q' : ℝ) := sorry

/-- Paper 1, Theorem 1.1, last sentence: no polynomial state bound for complementation
independent of the (finite) alphabet. -/
theorem readingNoPolyComplement :
    ¬ ∃ p : Polynomial ℕ, ∀ (α : Type) (_ : Finite α) (Q : Type) (_ : Fintype Q)
      (A : TwoWay α Q), ∃ (Q' : Type) (_ : Fintype Q') (B : TwoWay α Q'),
        B.Lang = {w | w ∉ A.Lang} ∧ Fintype.card Q' ≤ p.eval (Fintype.card Q) := sorry

/-- Paper 1, Corollary: determinization. -/
theorem readingDeterminization :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, 4 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      ∃ (Q : Type) (_ : Fintype Q) (A : TwoWay (Rel' (Fin (n - 2))) Q),
        Fintype.card Q = n ∧ A.Lang = livenessLang (Fin (n - 2)) ∧
        ∀ (Q' : Type) (_ : Fintype Q') (D : TwoWay (Rel' (Fin (n - 2))) Q'),
          D.IsDet → D.Lang = A.Lang →
          c * 2 ^ ((n - 4) / 127) ≤ (Fintype.card Q' : ℝ) := sorry

/-- Paper 1, Corollary, last sentence: no polynomial determinization independent of the alphabet. -/
theorem readingNoPolyDeterminize :
    ¬ ∃ p : Polynomial ℕ, ∀ (α : Type) (_ : Finite α) (Q : Type) (_ : Fintype Q)
      (A : TwoWay α Q), ∃ (Q' : Type) (_ : Fintype Q') (D : TwoWay α Q'),
        D.IsDet ∧ D.Lang = A.Lang ∧ Fintype.card Q' ≤ p.eval (Fintype.card Q) := sorry

/-- Paper 2, Theorem 1.1. -/
theorem readingLiveness (h : ℕ) (hh : 2 ≤ h) :
    (∃ (Q : Type) (_ : Fintype Q) (A : TwoWay (Rel' (Fin h)) Q),
        Fintype.card Q = h + 3 ∧ A.NoLeft ∧ A.Lang = livenessLang (Fin h)) ∧
    (∀ (Q : Type) (_ : Fintype Q) (D : TwoWay (Rel' (Fin h)) Q),
        D.IsDet → (D.Lang = livenessLang (Fin h) ∨ D.LangPos = livenessLang (Fin h)) →
        2 ^ ((h - 2) / 31) ≤ 4 * (Fintype.card Q + 2) ^ 2) ∧
    (∀ (Q : Type) (_ : Fintype Q) (D : TwoWay (Rel' (Fin h)) Q),
        D.IsDet → D.Lang = livenessLang (Fin h) →
        2 ^ ((h - 2) / 31) ≤ 4 * (Fintype.card Q + 1) ^ 2) := sorry

/-- Paper 2, Corollary: no polynomial simulation of 2NFAs by 2DFAs. -/
theorem readingNoPolynomialSimulation :
    ¬ ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (α : Type) (_ : Finite α) (Q : Type) (_ : Fintype Q) (A : TwoWay α Q),
        ∃ (Q' : Type) (_ : Fintype Q') (D : TwoWay α Q'),
          D.IsDet ∧ D.Lang = A.Lang ∧
          (Fintype.card Q' : ℝ) ≤ C * (Fintype.card Q : ℝ) ^ c := sorry

/-
Ambiguities and choices.

* Model: states `Q` a `Fintype` (the state count is `Fintype.card Q`); one initial state; accepting
  set; `trans : Q → Sym α → Set (Q × Dir)`, empty set = missing transition (branch rejects).
  Tape symbols `Sym α` = two distinct endmarkers `lm`, `rm` and letters. Head positions
  `0 … |w|+1` (`0` is the left endmarker, `|w|+1` the right one); the head starts at `0`, moves
  left/stay/right, and a configuration step requires both positions to be `≤ |w|+1`; a move left
  from `0` is excluded because `c.2 = c'.2 + 1` is impossible for `c.2 = 0`. Hence "moves beyond either
  endmarker are forbidden". No `ℕ` subtraction in the step relation.
* Acceptance: some finite computation reaches an accepting state; infinite nonaccepting computations
  reject automatically (they are not in `ReflTransGen`). Convention 1 (`Lang`) counts an accepting
  initial configuration; `LangPos` (convention 2) needs `TransGen`. Paper 1 and the first
  conventions of paper 2 use `Lang`.
* Deterministic: `IsDet` = every `(state, symbol)` has at most one successor (partial allowed).
  A 2DFA is a `TwoWay` with `IsDet`. "No left moves" is `NoLeft`.
* Alphabet `Σ_H = 𝓡_H` : `Rel' H = H → H → Prop` (all binary relations), finite for `H = Fin m`.
  Product in path order: `Relation.Comp A R a c = ∃ b, A a b ∧ R b c`; `relProd` folds from the left
  starting from `Eq` (the identity relation), so `r(ε) = Id` and `ε ∈ L_H` when `H` is nonempty.
  `L_H = {w | ∃ a b, r(w) a b}`. `H = {1,…,n-2}` is `Fin (n-2)`, `[h]` is `Fin h`; `n - 2`, `n - 4` are
  natural subtractions but only used under `n ≥ 4` (so no truncation). `OWL_h` is `livenessLang (Fin h)`.
* Paper 1 Theorem: the bound `½·2^⌊(n-4)/127⌋ - 1` is evaluated in `ℝ` (natural floor division in the
  exponent, as the floor of the quotient). "`A_n` recognizing `L_H`" is `A.Lang = livenessLang`; the
  complement is relative to `Σ_n^*`: `{w | w ∉ A.Lang}` over words of the alphabet. "Every 2NFA recognizing"
  quantifies over all state types `Q' : Type` with `Fintype`, and the bound is on `Fintype.card Q'`.
  The "in particular" sentence is a separate theorem; the polynomial `p` is a `Polynomial ℕ` and the alphabet
  ranges over all finite types in `Type`, bound compared with `p.eval (number of states of A)`. The
  statement is a negation of "exists a polynomial working for every finite alphabet".
* Paper 1 Corollary: constants `c > 0` (real) and `n₀` (I also required `4 ≤ n₀` to keep `n - 2`, `n - 4` honest).
  For `n ≥ n₀`, for the `n`-state automaton `A_n` of Theorem 1.1 I restate its existence in the same
  formula (the corollary refers to "the" `A_n`, not unique), and then every 2DFA with the same language
  has at least `c 2^⌊(n-4)/127⌋` states. This is existential in `A`, which is as in the Theorem (the
  `A_n` could differ from the theorem's `A_n` but the Theorem only gives existence; the corollary's `A_n` is
  intended to be that same automaton, so a stricter reading would reuse the Theorem's `A` — noted as a gap).
* Paper 2 Theorem: `n`-state NFA with `h + 3` states, no left moves, language `OWL_h` (convention 1;
  the text's NFA acceptance convention is not stated in the excerpt, I use the initial one). The DFA
  bound `4 (s+2)^2 ≥ 2^⌊(h-2)/31⌋` is in `ℕ` (no division besides the floor). Second sentence: with `s + 2`
  and either convention for the DFA's acceptance (`Lang` or `LangPos`); third: with `s + 1` under convention 1.
  The sentence "holds with either convention" is read as a claim about the 2DFA's convention;
  whether the NFA's language is also unchanged under the other convention is not formalized.
* Paper 2 Corollary: no absolute `C, c > 0` (reals) with every `n`-state 2NFA over every finite
  alphabet having an equivalent 2DFA with `≤ C n^c` states, where `n^c` is `Real.rpow` of the positive
  real `n` (the state set is nonempty since it contains `init`, so `n ≥ 1`). Convention 1 is used on both sides.
* Not formalized: nothing from the excerpts is omitted; the proof of the Corollary is not claimed.
-/

end ReaderB


namespace ReaderC

/-!
# Blind reading C, family O, paper O66: two-way automata and relation-product liveness

Model: a two-way automaton with state set `Q` and input alphabet `α`. The tape is the word
flanked by a left and a right endmarker; the head starts on the left endmarker in the initial
state. Transitions are sets of (state, move) pairs, so the same type covers partial and
nondeterministic rules; a deterministic rule is one with at most one successor.
Acceptance: some finite computation reaches an accepting state, and an accepting initial
configuration counts (the convention of the text's introduction).
-/

/-- Tape symbols: the left endmarker, the right endmarker, or an input letter. -/
inductive Sym (α : Type) where
  | lend : Sym α
  | rend : Sym α
  | sym : α → Sym α

/-- Head moves. -/
inductive Move where
  | left
  | right
  | stay

/-- A two-way automaton with states `Q` over alphabet `α`: initial state, accepting set,
and a transition relation `δ q a` giving the set of (successor state, move) pairs. -/
structure TWA (Q α : Type) where
  init : Q
  accept : Set Q
  δ : Q → Sym α → Set (Q × Move)

/-- The tape symbol scanned at position `p` on the tape of word `w`: position `0` is the left
endmarker, positions `1, …, |w|` carry the letters, position `|w| + 1` is the right endmarker. -/
def tapeAt {α : Type} (w : List α) (p : ℕ) : Sym α :=
  match p with
  | 0 => Sym.lend
  | k + 1 =>
    match w[k]? with
    | some a => Sym.sym a
    | none => Sym.rend

/-- One step of the automaton on input `w`. A move that would cross an endmarker is not a
step (position `0` and position `|w| + 1` are the bounds). -/
def TWA.Step {Q α : Type} (M : TWA Q α) (w : List α) (c c' : Q × ℕ) : Prop :=
  ∃ m : Move, (c'.1, m) ∈ M.δ c.1 (tapeAt w c.2) ∧
    ((m = Move.left ∧ 1 ≤ c.2 ∧ c'.2 + 1 = c.2) ∨
     (m = Move.right ∧ c.2 + 1 ≤ w.length + 1 ∧ c'.2 = c.2 + 1) ∨
     (m = Move.stay ∧ c'.2 = c.2))

/-- Acceptance: a finite computation from the initial configuration (initial state, head on
the left endmarker) reaches an accepting state. Reachability is reflexive, so an accepting
initial configuration counts. -/
def TWA.Accepts {Q α : Type} (M : TWA Q α) (w : List α) : Prop :=
  ∃ q ∈ M.accept, ∃ p : ℕ, Relation.ReflTransGen (M.Step w) (M.init, 0) (q, p)

/-- The language `L(M)`. -/
def TWA.Lang {Q α : Type} (M : TWA Q α) : Set (List α) :=
  {w | M.Accepts w}

/-- Deterministic: at most one successor for each state and scanned symbol. -/
def TWA.Det {Q α : Type} (M : TWA Q α) : Prop :=
  ∀ q a, (M.δ q a).Subsingleton

/-- No left moves. -/
def TWA.NoLeft {Q α : Type} (M : TWA Q α) : Prop :=
  ∀ q a q' m, (q', m) ∈ M.δ q a → m ≠ Move.left

/-- Relational product in path order: `(x,z) ∈ A B` iff `(x,y) ∈ A` and `(y,z) ∈ B`
for some `y`. -/
def relComp {H : Type} (A B : Set (H × H)) : Set (H × H) :=
  {p | ∃ q, (p.1, q) ∈ A ∧ (q, p.2) ∈ B}

/-- The identity relation `Id_H`. -/
def relId (H : Type) : Set (H × H) :=
  {p | p.1 = p.2}

/-- `r(w) = R_1 ⋯ R_k`, the product of a word of relations; the empty product is `Id_H`. -/
def relProd {H : Type} (w : List (Set (H × H))) : Set (H × H) :=
  w.foldl relComp (relId H)

/-- The liveness language `L_H = {w : r(w) ≠ ∅}` over the alphabet of all binary relations
on `H`. -/
def relLive (H : Type) : Set (List (Set (H × H))) :=
  {w | relProd w ≠ ∅}

/-- Theorem 1.1 of paper 1 (two-way nondeterministic complementation): for `n ≥ 4`, an
`n`-state 2NFA `A_n` recognizing `L_H` with `H = {1,…,n-2}` (modelled as `Fin (n-2)`) such that
every 2NFA for the complement `Σ_n^* ∖ L(A_n)` has at least `(1/2)·2^⌊(n-4)/127⌋ - 1` states. -/
theorem reading_O66_p1_thm11 :
    ∀ n : ℕ, 4 ≤ n →
      ∃ (Q : Type) (A : TWA Q (Set (Fin (n - 2) × Fin (n - 2)))),
        Nat.card Q = n ∧
        A.Lang = relLive (Fin (n - 2)) ∧
        ∀ (Q' : Type), Finite Q' →
          ∀ B : TWA Q' (Set (Fin (n - 2) × Fin (n - 2))),
            B.Lang = (A.Lang)ᶜ →
            (1 / 2 : ℝ) * (2 : ℝ) ^ ((n - 4) / 127) - 1 ≤ (Nat.card Q' : ℝ) := by
  sorry

/-- Corollary of paper 1 (determinization): absolute constants `c > 0` and `n_0` such that
every 2DFA for `L(A_n)` has at least `c · 2^⌊(n-4)/127⌋` states, and hence no polynomial state
bound independent of the alphabet determinizes all 2NFAs. -/
theorem reading_O66_p1_cor :
    (∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ, 4 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n →
        ∀ (Q : Type) [Finite Q] (D : TWA Q (Set (Fin (n - 2) × Fin (n - 2)))),
          D.Det → D.Lang = relLive (Fin (n - 2)) →
            c * (2 : ℝ) ^ ((n - 4) / 127) ≤ (Nat.card Q : ℝ)) ∧
    ¬ (∃ (C : ℝ) (k : ℕ), ∀ (α : Type) [Finite α] (Q : Type) [Finite Q] (M : TWA Q α),
        ∃ (Q' : Type) (D : TWA Q' α), Finite Q' ∧ D.Det ∧ D.Lang = M.Lang ∧
          (Nat.card Q' : ℝ) ≤ C * (Nat.card Q : ℝ) ^ k) := by
  sorry

/-- Theorem 1.1 of paper 2 (one-way liveness, two-way deterministic lower bound). For `h ≥ 2`:
(1) `OWL_h` is recognized by an NFA with `h + 3` states and no left moves; (2) every equivalent
deterministic two-way automaton with `s` states satisfies `4(s+2)^2 ≥ 2^⌊(h-2)/31⌋`; (3) with
the initially-accepting convention, `s + 2` may be replaced by `s + 1`. -/
theorem reading_O66_p2_thm11 :
    ∀ h : ℕ, 2 ≤ h →
      (∃ (Q : Type) (A : TWA Q (Set (Fin h × Fin h))),
        Nat.card Q = h + 3 ∧ A.NoLeft ∧ A.Lang = relLive (Fin h)) ∧
      (∀ (Q : Type) [Finite Q] (D : TWA Q (Set (Fin h × Fin h))),
        D.Det → D.Lang = relLive (Fin h) →
          2 ^ ((h - 2) / 31) ≤ 4 * (Nat.card Q + 2) ^ 2) ∧
      (∀ (Q : Type) [Finite Q] (D : TWA Q (Set (Fin h × Fin h))),
        D.Det → D.Lang = relLive (Fin h) →
          2 ^ ((h - 2) / 31) ≤ 4 * (Nat.card Q + 1) ^ 2) := by
  sorry

/-- Corollary of paper 2 (no polynomial simulation): there are no absolute constants
`C, c > 0` such that every `n`-state two-way nondeterministic automaton over every finite
alphabet has an equivalent two-way deterministic automaton with at most `C n^c` states. -/
theorem reading_O66_p2_cor :
    ¬ (∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (α : Type) [Finite α] (n : ℕ) (Q : Type) [Finite Q] (M : TWA Q α),
        Nat.card Q = n →
          ∃ (Q' : Type) (D : TWA Q' α), Finite Q' ∧ D.Det ∧ D.Lang = M.Lang ∧
            (Nat.card Q' : ℝ) ≤ C * (n : ℝ) ^ c) := by
  sorry

/-!
## Ambiguities and choices (reader C, O66)

1. Model. States `Q : Type` (finite by requirement, see point 6), alphabet `α : Type`. The
   tape is `⊢ w ⊣` with `⊢` the left and `⊣` the right endmarker, distinct from each other and
   from letters (`Sym`). Positions `0, …, |w|+1` are tape cells; the head starts at position `0`
   in the initial state.
2. Transitions. `δ q a` is a set of (successor state, move) pairs. A partial deterministic rule
   is a set of size at most one; "missing transitions reject" is the empty set. Nondeterminism
   is a set of size more than one. Stay moves are allowed. There are no extra heads, tapes,
   advice, or randomness.
3. Endmarkers. A move that would leave `[0, |w|+1]` is not a step (the text forbids it and
   missing transitions reject). I implemented this in `TWA.Step`: left needs position at least 1,
   right needs position plus one at most `|w|+1`. Nat subtraction is avoided by writing the
   left move as `c'.2 + 1 = c.2`.
4. Acceptance. A finite computation (reflexive-transitive closure of the step relation) reaching an
   accepting state, with the initial configuration itself counting. Nonaccepting infinite
   computations reject. The text's alternative convention (acceptance needs a positive
   transition into an accepting state) is not formalized; the theorem's (3) variant `s + 1`
   is stated under the text's main convention, which my model implements. The alternative
   convention would need `Relation.TransGen` and is not written.
5. Relation monoid. `R_H` = `Set (H × H)`. Composition `relComp` is in path order, as in the text.
   `Id_H` is `relId H`. The empty word's product is `Id_H` (`relProd [] = relId H`), so the
   empty word lies in `L_H` whenever `H` is nonempty, as the text says. `r(w) ≠ ∅` is the
   liveness condition. The text's `L_H = {w | r(w) ≠ ∅}` is `relLive H`.
6. Finite states. "n-state" is `Nat.card Q = n`. For `n ≥ 1` this forces `Q` finite, because
   `Nat.card` of an infinite type is `0`. Where a bound quantifies over arbitrary `Q'`, I added
   `Finite Q'` explicitly, so an infinite-state automaton cannot satisfy a bound by junk
   `Nat.card = 0`.
7. Universal alphabets. Quantifying over all `α : Type` with `[Finite α]` gives the
   "every finite alphabet" clause. The alphabet `R_H` for `|H| = h` is finite
   (`Set (Fin h × Fin h)` is finite), and the statements ask for complexity in `n` or `h` only.
8. Paper 1 specifics. `H = {1,…,n-2}` is modelled as `Fin (n-2)`, which has the same cardinality
   and the same relation monoid up to relabeling; `L_H` is identified with `relLive (Fin (n-2))`.
   `n - 2`, `n - 4` are natural subtraction, which is genuine because `n ≥ 4`. The exponent
   (the floor of n minus four, divided by 127) is natural-number division, which is the floor.
   The bound "one half times two to that exponent, minus one" is real, since it is subtracted
   in the reals and may be negative for small exponents; the bound on `Nat.card Q'` is in the reals.
9. Paper 1 complement. `Σ_n^* ∖ L(A_n)` is `(A.Lang)ᶜ` in `Set (List α)`, with the universe
   of all lists over the alphabet; `Σ_n^*` is the set of all lists over `Σ_n`. The complement
   statement quantifies over all 2NFAs `B` (any finite state set, nondeterminism allowed) with
   `B.Lang = (A.Lang)ᶜ`.
10. Paper 1 corollary. "Absolute constants `c > 0` and `n_0`": I put `0 < c` and an `n0 ≥ 4`
   (the `4 ≤ n0` clause is harmless and keeps `n - 4` genuine). The corollary is about the
   automaton `A_n` of the theorem; since the theorem says `A_n` recognizes `L_H`, the
   corollary's 2DFA condition is `D.Lang = relLive (Fin (n-2))`, which does not depend on
   which `A_n` was chosen. This is a reading of "the language of `A_n`", and it is the stronger
   reading (every 2DFA for `L_H`). The "hence" clause is written as the non-existence of a
   polynomial `C n^k`-type bound for determinization of all 2NFAs over all finite alphabets,
   with the state count `Nat.card Q` of the source.
11. Paper 2 theorem, the two sentences. (1) NFA with `h + 3` states and `NoLeft`, recognizing
   `OWL_h`. (2) For each deterministic two-way `D` with `s = Nat.card Q` states recognizing `OWL_h`,
   four times `(s+2)^2` is at least `2` to the natural exponent that is the floor of `(h-2)`
   divided by 31 (natural division). (3) The variant with `s + 1`, stated under the convention that
   an initially accepting configuration counts (my model's convention). The variant is a separate
   conjunct; it is stronger than (2) under this convention. The theorem's `h ≥ 2` gives genuine
   `h - 2`.
12. Paper 2 corollary. "Absolute constants `C, c > 0`": I used real `C, c` with `0 < C` and `0 < c`.
   The equivalence is language equality over the same alphabet; the bound is `C · n^c` with
   `n = Nat.card Q` and `(n : ℝ) ^ c` a real power with `n ≥ 1` (the state set is nonempty
   because the initial state exists, so `n ≥ 1`). The Corollary's proof sketch gives a numeric
   bound that I did not formalize (it is in the proof, not the statement).
13. Not formalized: the proof of the corollary of paper 2 (its displayed numeric bound is in
   the proof, not the statement); the excerpt's line about "Theorem" at the end of the paper 1
   introduction is a dangling sentence with no claim of its own; the introductory references
   to Sakoda and Sipser and to Kapoutsis are bibliographic only.
14. Mathlib names used: `Relation.ReflTransGen`, `List.foldl`, `Set.Subsingleton`, `Nat.card`,
   `Finite`. No Mathlib automata library is used; the model is written from the text.
-/

end ReaderC

