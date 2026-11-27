# Blind reading brief: target O, families O7 "A Complete Local Domain without a Small Cohen–Macaulay Module", O8 "The Falconer distance conjecture in all dimensions", O9 "The irrationality exponent of π is 2" (OpenAI release)

Committed before any reader runs. Readers A (Opus), B (Sonnet), C (Haiku), each alone, all three families.
You have NOT seen, and must not look for, any Lean formalization of these claims. Read only this brief and
the files in `smallcm/sources/`, `falconer/sources/`, `piexp/sources/` (verbatim TeX lines; sha256 prefixes:
small-CM paper.tex 76d8de92a9ef5850, Falconer 00_introduction.tex 4e12b57b3418561a, π main.tex
1479652f0081d432). No other file, no web. You may read Mathlib's source
(/home/claude/formalization/.lake/packages/mathlib) for names.

For each family write ONE Lean 4 file, `import Mathlib` only, at `<family>/<your letter>/reading.lean`,
with every definition the claim needs written by you from the source (use Mathlib's notions where they
exist: depth may need your own definition — say so), and the headline theorem(s) as
`theorem reading… : … := sorry`, as literally as possible:

- O7 (smallcm): Theorem 1.1, and the abstract's "disproves the domain form of the small Cohen–Macaulay
  module conjecture" as a second theorem (the negation of the conjecture as the source states it).
- O8 (falconer): Theorem 1.1 (every compact E ⊆ ℝ^d, d ≥ 2, with dim_H E > d/2 has a distance set of
  positive Lebesgue measure, or as the source states it).
- O9 (piexp): Theorem 1.1 (both the "irrationality exponent is 2" sentence with the source's definition of
  μ(x), and the "more precisely" inequality), and the abstract's consequence about the Flint–Hills series.

In a comment block below each file's code: every ambiguity and your choice; which claims are proved in the
source and which only stated as consequences. Avoid junk values (`sSup` of an empty or unbounded set,
`tsum` of a non-summable family, rpow of negatives, ℕ subtraction) and say how. Check each file compiles:
`cd /home/claude/formalization && export PATH=$HOME/.elan/bin:$PATH && lake env lean <file>` (`sorry` only in
the claim theorems).
