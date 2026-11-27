import Mathlib

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
