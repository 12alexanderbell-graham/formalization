# Blind reading brief: target R (Alpöge's claimed proof of RH and GRH, 2026-11-20)

Committed before any reader runs. Readers: A (Opus), B (Sonnet), C (Haiku): three different models,
each alone, each sees only this brief and `sources/remark_pdftotext.txt`.

You have NOT seen, and must not look for, any Lean formalization of this claim. Do not open any file
outside `runs/2026-11-27T0628Z/R/` and do not search the web. In that folder read only this file and
`sources/remark_pdftotext.txt` (the text of the four-page note, `remark.pdf`, sha256
3fc97784b71ddd44ff8aa0a177e99622a1c61b13cfa843a0989ee4a7a0cfeb8d, extracted with pdftotext).

## The claim, verbatim from the note (page 1)

"I believe I have, working with Claude, discovered a proof of the Riemann Hypothesis. In fact, the
method easily extends much further, resolving the so-called Generalized Riemann Hypothesis, and I
expect, with more time, the Extended Riemann Hypothesis too. Claude and I have also formalized the
arguments without assumptions."

Page 4, last item of the timeline: "20. 11/16/26: GRH."

The note states no theorem formally. Read the claims as a number theorist would, with the standard
textbook meaning of each term: the Riemann Hypothesis (Riemann zeta function), and the Generalized
Riemann Hypothesis as it is standardly meant for **Dirichlet L-functions** (the Lean archive is said
to cover Dirichlet L-functions; if you think "GRH" standardly means more than that, write the
Dirichlet version as asked AND say in your comment block what broader statement the word could mean).

## Task

Write ONE self-contained Lean 4 file, `import Mathlib` only (Mathlib of Lean v4.35.0), to the path
given in your instructions, containing:

1. `def ReadingRH : Prop := ...` — the Riemann Hypothesis, as literally as the standard statement
   allows (every nontrivial zero of ζ has real part 1/2). Use Mathlib's `riemannZeta : ℂ → ℂ`.
   Mathlib's `riemannZeta` is defined on all of ℂ, including at the pole s = 1, where it takes a
   junk value; decide how your statement handles s = 1 and the trivial zeros, and say why.
   Do NOT use Mathlib's `RiemannHypothesis` constant; write the condition out yourself.
2. `def ReadingGRH : Prop := ...` — GRH for Dirichlet L-functions, as you read it standardly
   (which characters: primitive only, or all; which zeros: nontrivial ones, however you define
   them; how the pole of the principal character is handled). Use Mathlib's
   `DirichletCharacter ℂ N` and `DirichletCharacter.LFunction χ : ℂ → ℂ` (defined on all of ℂ,
   junk value at a pole). Write it as literally as you can.
3. If you think a second, equally standard reading of GRH exists (e.g. all characters vs. only
   primitive ones; zeros in the critical strip vs. all non-trivial zeros), add
   `def ReadingGRH' : Prop := ...` with that reading.
4. Below the code, a comment block listing every place where the claim or the standard
   definition is ambiguous, which reading you chose, and why; and any claim in the note (other
   than RH and GRH) that is stated as proved, with the sentence quoted.

Avoid junk values: never let the statement depend on the value of a function at its pole, on ℕ
subtraction, or on division by a possibly zero term, unless you say so. The file must parse and
elaborate with `lake env lean` (use `sorry` nowhere: these are `def`s of `Prop`s, no proofs needed).
If you can, check it compiles; if you cannot run Lean, say so.
