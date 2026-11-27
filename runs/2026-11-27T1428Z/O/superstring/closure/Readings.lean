import Mathlib

/-! # Target O, family superstring: the three blind readings of run 2026-11-27T1428Z (brief 44efa61), concatenated unchanged
apart from the repeated `import Mathlib` lines, so a closure can import them as one module. -/


/-!
Reader A, family O51 (superstring): Theorem 1.1 of "A factor-two approximation for shortest
common superstring", read from the abstract and 01-introduction.tex lines 1-12 only.
-/

namespace ReaderA

/-- An ordinary finite string: a list of symbols, each symbol a natural-number label. -/
abbrev Str := List ℕ

/-- `T` is a common superstring of the collection `S`: every member of `S` occurs in `T` as a
contiguous substring (`List.IsInfix`). -/
def IsCommonSuperstring (S : List Str) (T : Str) : Prop :=
  ∀ s ∈ S, s <:+: T

/-- A common superstring always exists (the concatenation), so `OPT` below is a genuine
minimum, never a junk value. -/
theorem exists_commonSuperstring_length (S : List Str) :
    ∃ n, ∃ T, IsCommonSuperstring S T ∧ T.length = n :=
  ⟨_, S.flatten, fun _ hs => List.infix_of_mem_flatten hs, rfl⟩

open Classical in
/-- `OPT(S)`: the minimum possible length of a common superstring of `S`. -/
noncomputable def OPT (S : List Str) : ℕ :=
  Nat.find (exists_commonSuperstring_length S)

/-- Tape alphabet of the explicit representation: bits of a symbol label, an end-of-symbol
marker, and an end-of-string (boundary) marker. -/
inductive EncSym
  | bit (b : Bool)
  | endSym
  | endStr
  deriving DecidableEq, Fintype

/-- A symbol label `a ∈ ℕ` is written in binary (Mathlib's `Computability.encodeNat`) followed by
an end-of-symbol marker, so every symbol occupies at least one tape cell. -/
def encodeSymbol (a : ℕ) : List EncSym :=
  (Computability.encodeNat a).map EncSym.bit ++ [EncSym.endSym]

/-- A string is the concatenation of its encoded symbols followed by a boundary marker. -/
def encodeString (s : Str) : List EncSym :=
  s.flatMap encodeSymbol ++ [EncSym.endStr]

/-- The explicit representation of the input collection: its strings' encodings in order.
Its length is the total encoded input size `N`. -/
def encodeInput (S : List Str) : List EncSym :=
  S.flatMap encodeString

/-- The output string is represented the same way as one input string. -/
def encodeOutput (T : Str) : List EncSym :=
  encodeString T

/-- Theorem 1.1. There is a deterministic algorithm (a Mathlib multi-stack Turing machine
`FinTM2`, which is deterministic) computing a function `alg` from encoded inputs to encoded
outputs in time bounded by a polynomial in the encoded input length, such that on every finite
collection `S` of explicitly represented strings `alg S` is a common superstring of `S` with
`len(alg S) ≤ 2·OPT(S)`. -/
theorem readingSuperstring :
    ∃ alg : List Str → Str,
      Nonempty (Turing.TM2ComputableInPolyTime encodeInput encodeOutput alg) ∧
      ∀ S : List Str, IsCommonSuperstring S (alg S) ∧ (alg S).length ≤ 2 * OPT S := sorry

end ReaderA

/-
MODELLING CHOICES (asked for by the brief)

* "Algorithm", "deterministic". An algorithm is a function `alg : List Str → Str` together with
  a witness `Turing.TM2ComputableInPolyTime encodeInput encodeOutput alg` (Mathlib,
  `Mathlib/Computability/TuringMachine/Computable.lean`): a `FinTM2` machine (finitely many
  stacks, finite label set, finite internal state set, finite input alphabet) whose input
  alphabet is equivalent to `EncSym` and output alphabet equivalent to `EncSym`, which on the
  encoded input halts with the encoded output on its output stack. Its step function
  `cfg → Option cfg` is a function, so the machine is deterministic. Since the algorithm is a
  function of the input, the theorem asserts it outputs one specific superstring per input.

* "Polynomial in the total encoded input size". `TM2ComputableInPolyTime` provides a polynomial
  `p : Polynomial ℕ` such that the machine halts within `p.eval (encodeInput S).length` steps.
  `(encodeInput S).length` is my `N`: the total number of tape symbols of the explicit
  representation, including symbol labels and boundaries. A constant-size alphabet makes cells
  and bits equivalent up to a constant factor (3-4 letters vs. 2 bits each), so "bit length"
  vs "cell count" does not affect polynomiality.

* Encoding of symbols and strings. Symbols are natural-number labels (an unbounded alphabet, so
  labels genuinely cost their encoded length, as the source says "operations on symbol labels
  are charged for their encoded lengths"). A symbol `a` is `encodeNat a` (binary, Mathlib) in
  bits, then `endSym`; a string is its symbols then `endStr`; a collection is the concatenation
  of its strings. Each symbol and each boundary occupies at least one cell, so `L, |S| ≤ N`, as
  in the source. The encoding is injective (binary is injective by `decode_encodeNat` and the
  markers delimit), so the machine sees exactly the input. The output `T` is encoded as one
  string. Any finite alphabet embeds in ℕ, so ℕ-labels cover every explicitly represented
  alphabet.

AMBIGUITIES AND CHOICES

1. "Finite collection S of strings": modelled as a `List Str` (the explicit representation is an
   ordered list; duplicates and empty strings are allowed). Superstring-ness and OPT depend only
   on the underlying set, so this is harmless; the algorithm must work on every list.

2. "Contains every member as a contiguous substring": `List.IsInfix` (`<:+:`).

3. OPT. Defined as `Nat.find` of the (proved) existence of a common superstring length, i.e. the
   least `n` that is the length of some common superstring. Since a common superstring always
   exists (concatenation), this is a genuine minimum; no `sInf ∅` junk. The output string `T` may
   use any ℕ-symbols; using symbols absent from `S` never shortens a superstring, so OPT over
   ℕ-strings equals OPT over the alphabet of `S`.

4. "2·OPT": natural-number multiplication; no subtraction or division anywhere.

5. Empty collection: OPT = 0 and the algorithm must output the empty string; read literally
   ("every finite collection").

6. The abstract's remark that the guarantee concerns "the algorithm constructed here, not
   Greedy" is not part of the formal claim; the theorem is existential in the algorithm.

7. Known looseness of Mathlib's `FinTM2`: only the input stack alphabet is required finite;
   other stacks' alphabets are arbitrary types, but they can only hold values pushed from the
   finite state space, so this does not add computational power. Output alphabet is equivalent
   to the finite `EncSym`.
-/


namespace ReaderB

open Computability Turing

/-- A string over an infinite symbol set: symbols are labels in `ℕ`. -/
abbrev Str := List ℕ

/-- `T` is a common superstring of `S`: every member occurs as a contiguous substring. -/
def IsCommonSuperstring (S : List Str) (T : Str) : Prop :=
  ∀ s ∈ S, s <:+: T

/-- `OPT(S)`, the minimum length of a common superstring. The set is nonempty
(the concatenation of `S` is a common superstring), so `sInf` is the genuine minimum. -/
noncomputable def OPT (S : List Str) : ℕ :=
  sInf {n | ∃ T : Str, IsCommonSuperstring S T ∧ T.length = n}

/-- Encoding of a symbol label `n` : the binary numeral of `n + 1` (nonempty, so that
distinct symbols and boundaries are unambiguous), each bit costing one tape cell. -/
def encodeSymbol (n : ℕ) : List Γ' :=
  (encodeNat (n + 1)).map Γ'.bit

/-- Encoding of a string: `bra`, symbol codes separated by `comma`, `ket`. -/
def encodeStr (s : Str) : List Γ' :=
  Γ'.bra :: ((s.map encodeSymbol).intersperse [Γ'.comma]).flatten ++ [Γ'.ket]

/-- Encoding of a collection: the concatenation of the encodings of its strings. -/
def encodeCollection (S : List Str) : List Γ' :=
  (S.map encodeStr).flatten

/-- Theorem 1.1. "Algorithm": a deterministic multi-stack Turing machine (Mathlib's
`TM2`) computing a total function `f` from collections to strings. "Polynomial in the total
encoded input size": the number of steps on input `S` is at most `p(N)` for a polynomial `p`,
where `N = (encodeCollection S).length` is the number of tape cells of the encoding, in which
each symbol label is charged its binary length. -/
theorem reading_superstring :
    ∃ f : List Str → Str,
      Nonempty (TM2ComputableInPolyTime encodeCollection encodeStr f) ∧
      ∀ S : List Str, IsCommonSuperstring S (f S) ∧ (f S).length ≤ 2 * OPT S := sorry

/-! ## Comments: ambiguities and choices

* Algorithm: a deterministic algorithm is a `Turing.TM2ComputableInPolyTime` machine
  (a deterministic TM2 with finite stack alphabets, polynomial step bound `time.eval N`
  where `N` is the input tape length). It exists as `Nonempty` (a Prop), together with the
  function `f` it computes. The machine's input alphabet is `Γ'` (blank, bit, bra, ket,
  comma) via the equivalence built into the structure.
* Symbols: labels are natural numbers, unbounded (no fixed alphabet), encoded in binary as
  the bits of `n + 1` (shifted so every symbol has a non-empty code and `[]` vs `[0]` are
  distinguished). Strings are `bra ... ket` with commas between symbols, collections are
  concatenations. Each symbol and boundary costs at least one cell, so `L, |S| ≤ N`.
  I did not prove the encoding injective (not needed for the claim; the comma/bra/ket
  separators make it so).
* Output encoding is `encodeStr`, the same string encoding (output length counted in
  symbols is `(f S).length`).
* "Finite collection": `List Str` (duplicates allowed, harmless). "Ordinary strings":
  strings of symbols with no wildcards; the empty string is allowed. Substring: contiguous
  (`<:+:` is `List.IsInfix`).
* `OPT` uses `sInf` on ℕ, nonempty set (concatenation witness) so no junk value; `2 * OPT`
  has no subtraction. For the empty collection OPT = 0 and the output must be `[]`.
* Claimed correctness is for every collection, with time bound relative to the encoding
  of that collection; behaviour on tapes that are not encodings is unconstrained.
-/

end ReaderB


open Turing

namespace ReaderC

noncomputable section

/-- Self-delimiting binary code of a natural-number symbol label: a unary run of `true` whose length
is the number of bits of `n`, then `false`, then the binary digits of `n` (`Nat.bits`,
little-endian). -/
def encNat (n : ℕ) : List Bool :=
  List.replicate (Nat.bits n).length true ++ false :: Nat.bits n

/-- Encoding of one explicitly represented string of symbol labels: each symbol is the tag `true`
followed by its label code. -/
def encSyms (w : List ℕ) : List Bool :=
  w.flatMap (fun n => true :: encNat n)

/-- Encoding of a finite family of strings: each string is encoded by `encSyms`, followed by the
boundary tag `false`. Its length is the total bit length `N` of the input. -/
def encStrings (S : List (List ℕ)) : List Bool :=
  S.flatMap (fun w => encSyms w ++ [false])

/-- `T` is a common superstring of `S`: every member of `S` is a contiguous substring of `T`. -/
def IsCommonSuperstring (T : List ℕ) (S : List (List ℕ)) : Prop :=
  ∀ s ∈ S, List.IsInfix s T

/-- The optimum `OPT(S)`: the least length of a common superstring. The set is nonempty for every
`S`, since the concatenation of all members of `S` is a common superstring, so `sInf` is a genuine
minimum and no junk value arises. -/
def OPT (S : List (List ℕ)) : ℕ :=
  sInf {n | ∃ T : List ℕ, T.length = n ∧ IsCommonSuperstring T S}

/-- Theorem 1.1: a deterministic polynomial-time algorithm, realised as a Turing machine `M` (TM2)
computing `f` in time polynomial in the encoded input size `(encStrings S).length`, whose output is a
common superstring of length at most `2 · OPT S`. -/
theorem reading_superstring :
    ∃ (f : List (List ℕ) → List ℕ) (M : TM2ComputableInPolyTime encStrings encSyms f),
      ∀ S : List (List ℕ), IsCommonSuperstring (f S) S ∧ (f S).length ≤ 2 * OPT S := sorry

end

end ReaderC

/-
Comment block (blind reading C, family O51, source
`superstring/sources/abstract_and_introduction_lines1-12.tex` only).

Modelling choices and ambiguities, all my decisions:

* "Deterministic algorithm, polynomial in the total encoded input size": modelled by Mathlib's
  `Turing.TM2ComputableInPolyTime ea eb f`. This is a single deterministic TM2 machine `M` that, on
  every input `S`, halts with output `encSyms (f S)` after at most `time.eval (|ea S|)` steps, where
  `time` is a polynomial over ℕ. The machine is deterministic, since TM2 has no nondeterminism. The
  polynomial is in the length of the input encoding, i.e. the total bit length `N`, as the brief asks.
* "Encoding of symbols and strings": the alphabet is `Bool`. A symbol label `n ∈ ℕ` is encoded
  self-delimitingly by `encNat` (unary bit-length, separator, then `Nat.bits n`), so a label costs
  `O(log n)` bits and each symbol costs one extra tag bit. A string is a sequence of symbols, each
  tagged `true`, followed by the boundary tag `false`. The whole family is `encStrings`. The output
  string is encoded by `encSyms`. This is a prefix-decodable code. Any other reasonable encoding
  changes the time bound only by a polynomial, so the theorem is unaffected.
* "Ordinary strings" are `List ℕ` over the symbol set ℕ. "Explicit representation" is the encoding
  above. The family is a `List (List ℕ)`, so duplicates are allowed. A "finite collection" is read as
  a finite list.
* `L` and `|S|` are not separately modelled. They are bounded by the input bit length `N`, as the
  paper notes, and the time bound is a polynomial in `N`.
* `OPT S` is `sInf` over lengths of common superstrings. The set is nonempty, because the concatenation
  of the members of `S` is a common superstring, so `OPT` is a true minimum and no `sInf ∅ = 0` junk
  arises. `S = []` gives `OPT = 0`, which is correct.
* Superstring: `List.IsInfix s T` is "contiguous substring". The predicate is defined directly and not
  via `OPT`'s set, to keep the statement literal.
* The bound `len T ≤ 2 · OPT S` is in ℕ with no subtraction, so there is no truncation issue.
* The statement is `∃ f, ∃ M : TM2ComputableInPolyTime encStrings encSyms f, ...`. Here `M` witnesses
  that `f` is poly-time computable with respect to these encodings, and the second conjunct says that
  `f` outputs a common superstring within factor two of optimum on every input.
* The file has `import Mathlib` only and is wrapped in `namespace ReaderC`. The theorem is `sorry`.
  It compiles with `lake env lean`, with only the one `sorry` warning.
-/
