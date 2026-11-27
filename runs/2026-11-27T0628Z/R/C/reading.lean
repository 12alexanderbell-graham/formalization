import Mathlib

/-!
# Blind reading of target R (Alpöge's claimed proof of RH and GRH, 2026-11-20)

Reader C. Written only from `BRIEF.md` and `sources/remark_pdftotext.txt`.

## Riemann Hypothesis: `ReadingRH`

Statement: every zero `s` of `riemannZeta` with `0 < Re s < 1` has `Re s = 1/2`.

Handling of the special points:
* "Nontrivial zero" is read as "zero in the open critical strip `0 < Re s < 1`".
  This is the standard meaning (Titchmarsh, Davenport). It excludes the trivial zeros
  `s = -2n` (n ≥ 1) automatically, since they have real part `< 0`.
* The pole `s = 1` is excluded automatically, since `Re 1 = 1` is not `< 1`.
  So the statement never inspects the junk value `riemannZeta 1`.
* No ℕ subtraction, no division by a possibly-zero term; `1 / 2 : ℝ` is a fixed constant.

## Generalized Riemann Hypothesis for Dirichlet L-functions: `ReadingGRH`

Reading chosen: **primitive** characters only, all moduli `N > 0`.
Zeros: zeros of `DirichletCharacter.LFunction χ` in the open strip `0 < Re s < 1`.

* Primitivity is spelled out in `ReadingIsPrimitive` (conductor equal to `N`):
  no proper divisor `d` of `N` induces `χ`. Concretely, for each proper divisor
  `d` of `N` there are naturals `a, b` coprime to `N` with `a ≡ b [MOD d]` and
  `χ a ≠ χ b`. For `N = 1` the condition is vacuous, so the unique character
  (whose L-function is ζ) counts as primitive, matching the usual convention.
* The principal character mod `N > 1` is not primitive, so it is excluded. Its
  L-function has a pole at `s = 1`, which the strip condition excludes anyway.
* Non-primitive characters are excluded by the primitive reading. Their L-functions
  differ from the primitive ones by finitely many Euler factors whose zeros lie on
  `Re s = 0`, outside the strip. So `ReadingGRH'` below is mathematically equivalent
  to `ReadingGRH`, but written as its own statement.

## Second reading: `ReadingGRH'`

All characters mod `N > 0`, zeros in the open strip. This is the "all characters"
reading. It is equivalent to `ReadingGRH` given the Euler-factor analysis above.

## Ambiguities and the note's claims (comment block)

1. Which characters: primitive only (`ReadingGRH`) or all (`ReadingGRH'`). Chose primitive.
   The two are equivalent by standard facts, but the file states both.
2. Which zeros are "nontrivial": chose "in the open critical strip" over
   "not in the set of trivial zeros". These coincide by standard facts (the zeros of ζ
   and of primitive L(·,χ) outside the strip are exactly the trivial ones).
3. The pole of ζ at `s = 1` and the principal character's pole: excluded by the strip
   condition, not by the junk value.
4. "GRH" could also mean the Generalized Riemann Hypothesis for Hecke L-functions,
   for automorphic L-functions, or for Dedekind zeta functions of number fields.
   Those are strictly broader than Dirichlet L-functions. The brief says the standard
   reading is Dirichlet, and the file uses that. The note itself never defines GRH.
5. "Extended Riemann Hypothesis" (ERH): in the note this is stated only as an
   expectation ("I expect, with more time"). Commonly ERH means GRH for Dedekind zeta
   functions of number fields, or for all Hecke L-functions. Not formalized here.
6. Claims in the note other than RH and GRH:
   * Page 1, quoted: "Claude and I have also formalized the arguments without assumptions."
     Stated as done. Not formalized here (no Lean in this file).
   * Page 2, quoted: "The argument is incredibly long at the moment, and while its
     formalization is finished and it is routine to produce a huge, unreadable document
     containing sufficient detail ..." Stated as done.
   * Page 4 timeline, item 9, quoted: "with proven divisibility via Chowla-Selberg, Weyl,
     and Siegel mass." Stated as proven.
   * Page 4 timeline, item 8, quoted: "wins multiplicity m." Stated as achieved.
   * Page 3, quoted: "we were going to win". A claim of victory, not a precise theorem.
   * The note also says "I believe I have ... discovered a proof" (hedged), and
     "I expect ... the Extended Riemann Hypothesis" (a prediction, not a claim of proof).
     Footnote 6 "I believe vanishing of a number of K-groups of Z follows" is hedged.
   * Page 3, footnote 4, quoted: "the Lean should suffice to clarify everything." This
     refers to a Lean archive the reader does not have. Not a theorem claim.
   None of these theorems is stated formally in the note. Only the quoted sentences
   are checkable claims.
7. The note's "Theorem 1" is mentioned on page 2 only in passing ("if σ ≠ 1/2 then
   σ > 1/2 or σ < 1/2"). Not formalized.

Lean check: not run successfully. `lake env lean` reports that `Mathlib.olean` is not
present in the search path, so the Mathlib build is not available yet. The signature
`DirichletCharacter.LFunction χ s` is taken from the brief and is unverified.
-/

/-- The Riemann Hypothesis, as a `Prop`.

Every zero `s` of `riemannZeta` in the open critical strip `0 < Re s < 1` has real part `1/2`.
Trivial zeros (at `-2n`) and the pole at `s = 1` lie outside the strip, so they are excluded. -/
def ReadingRH : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

/-- `χ : DirichletCharacter ℂ N` is primitive: its conductor is `N`.
Equivalently, no proper divisor `d` of `N` induces `χ`. Induced from `d` means
`χ a = χ b` whenever `a ≡ b (mod d)` and both `a`, `b` are coprime to `N`. -/
def ReadingIsPrimitive (N : ℕ) (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ d : ℕ, d ∣ N → d ≠ N →
    ∃ a b : ℕ, Nat.Coprime a N ∧ Nat.Coprime b N ∧ a ≡ b [MOD d] ∧
      χ (a : ZMod N) ≠ χ (b : ZMod N)

/-- GRH for Dirichlet L-functions, primitive-character reading.

For every modulus `N > 0` and every primitive character `χ` mod `N`, every zero `s` of
`DirichletCharacter.LFunction χ` in the open critical strip `0 < Re s < 1` has `Re s = 1/2`.
The trivial zeros and the pole at `s = 1` lie outside the strip. -/
def ReadingGRH : Prop :=
  ∀ N : ℕ, 0 < N → ∀ χ : DirichletCharacter ℂ N, ReadingIsPrimitive N χ →
    ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

/-- GRH for Dirichlet L-functions, all-characters reading.

Same as `ReadingGRH`, but for every character `χ` mod `N > 0`, primitive or not.
Mathematically equivalent to `ReadingGRH`: the extra Euler factors of imprimitive
characters have zeros only on `Re s = 0`. -/
def ReadingGRH' : Prop :=
  ∀ N : ℕ, 0 < N → ∀ χ : DirichletCharacter ℂ N,
    ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2
