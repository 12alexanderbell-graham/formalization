import Mathlib

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
