import Mathlib

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
