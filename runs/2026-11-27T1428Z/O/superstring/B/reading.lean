import Mathlib

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
