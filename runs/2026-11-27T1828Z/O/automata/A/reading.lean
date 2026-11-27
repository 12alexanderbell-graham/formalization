import Mathlib

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
