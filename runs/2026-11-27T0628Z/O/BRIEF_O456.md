# Blind reading brief: target O, families O4 "The Euclidean plane is not five-colorable", O5 "The additive indecomposability of the primes" (Ostmann), O6 "A power saving for square-difference-free sets" (OpenAI release)

Committed before any reader runs. Readers A (Opus), B (Sonnet), C (Haiku), each alone, all three families.
You have NOT seen, and must not look for, any Lean formalization of these claims. Read only this brief and
the files in `plane5/sources/`, `ostmann/sources/`, `sqdiff/sources/` (verbatim TeX lines; sha256 prefixes:
plane introduction.tex 41222c5b4e8be335, Ostmann 01-introduction.tex 58d391e18a6bbb89, square-difference
introduction.tex ab0e277a6aba1da9). No other file, no web. You may read Mathlib's source
(/home/claude/formalization/.lake/packages/mathlib) for names.

For each family write ONE Lean 4 file, `import Mathlib` only, at `<family>/<your letter>/reading.lean`,
with every definition the claim needs written by you from the source, and the headline theorem(s) as
`theorem reading… : … := sorry`, as literally as possible:

- O4 (plane5): Theorem 1.1 — no proper five-coloring of the plane "even when arbitrary color classes are
  allowed" (no measurability), and its stated consequence 6 ≤ χ(ℝ²) ≤ 7 (define χ(ℝ²) yourself without
  junk values, e.g. as a statement about which k admit a proper coloring). Say which parts the source
  proves and which it cites.
- O5 (ostmann): Theorem 1.1 (Ostmann's conjecture) and Theorem 2.x if stated in your excerpt
  ("two infinite summands"); use the source's ℕ₀ and its primes.
- O6 (sqdiff): Theorem 1.1 (|A| ≤ C N^{1−c}) and its "Equivalently" sentence, as two theorems.

In a comment block below each file's code: every ambiguity and your choice. Avoid junk values (ℕ
subtraction, rpow of negatives, `sSup`/`sInf` of possibly empty or unbounded sets). Check each file
compiles: `cd /home/claude/formalization && export PATH=$HOME/.elan/bin:$PATH && lake env lean <file>`
(`sorry` only in the claim theorems).
