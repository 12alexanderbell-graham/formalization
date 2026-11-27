import Mathlib

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
