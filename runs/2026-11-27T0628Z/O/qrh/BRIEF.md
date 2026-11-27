# Blind reading brief: target O, family "The Quasi-Riemann Hypothesis" (OpenAI release, github.com/openai/math)

Committed before any reader runs. Readers A (Opus), B (Sonnet), C (Haiku), each alone.

You have NOT seen, and must not look for, any Lean formalization of this claim. Read only this brief
and the two files in `sources/` (verbatim excerpts of the two manuscripts' TeX: `paper_sep30_lines.tex`
from paper.tex of 30 September 2026, sha256 42a5ee0f…a6c3; `paper2_oct5_lines.tex` from paper2.tex of
5 October 2026, sha256 d9a8f15a…0d4d). Do not open any other file, do not search the web.

## Task

Write ONE Lean 4 file, `import Mathlib` only (Lean v4.35.0 Mathlib), to the path you are given, with:

1. `def ReadingZeta (σ₀ : ℝ) : Prop` — "ζ(s) has no zero in Re s > σ₀", using Mathlib's `riemannZeta`
   (defined on all of ℂ; junk value at the pole s = 1: decide and say how you handle it).
2. `def ReadingDirichlet (σ₀ : ℝ) : Prop` — "every Dirichlet L-function has no zero in Re s > σ₀, a pole
   at s = 1 for a principal character allowed", using `DirichletCharacter ℂ N` and
   `DirichletCharacter.LFunction` (junk value at its pole). Say which characters the manuscripts mean
   (primitive only, or every character mod every N) and write that; if the two manuscripts differ, write
   both (`ReadingDirichletPrim`, …).
3. `def ReadingHecke (σ₀ : ℝ) : Prop` — "every finite-order Hecke L-function over Q(√-3) has no zero in
   Re s > σ₀". Mathlib has no Hecke L-functions. Write it without defining the continuation yourself:
   quantify over every function `f : ℂ → ℂ` that is holomorphic on ℂ ∖ {1} (`DifferentiableOn ℂ f {1}ᶜ`)
   and equals the manuscript's Dirichlet series `∑_{𝔞 ≠ 0} η(𝔞) N𝔞^{-s}` for Re s > 1, and say that such
   `f` has no zero in Re s > σ₀ (s ≠ 1 where the pole is allowed). Define the finite-order Hecke
   characters over `𝓞 (CyclotomicField 3 ℚ)` (or another model of Q(√-3) you prefer) as literally as the
   source allows (a character of the ray class group mod 𝔣, extended by zero to ideals not coprime to 𝔣),
   and the sum over nonzero integral ideals. If a literal definition of the ray class group is out of
   reach in Mathlib, give the closest faithful one and say precisely what it changes.
4. `theorem reading_sep30 : ReadingHecke (7/8) ∧ ReadingDirichlet (7/8) ∧ ReadingZeta (7/8) := sorry` and
   `theorem reading_oct5 : ReadingHecke (11/12) ∧ ReadingDirichlet (11/12) ∧ ReadingZeta (11/12) := sorry`
   (adapt to the character sets you chose).
5. Below the code, a comment block: every ambiguity and your choice; and every difference between the two
   manuscripts' headline claims (quote them).

Avoid junk values (pole, ℕ subtraction, division by zero, `tsum` of a non-summable family: say why your
sums converge where you use them). Check it compiles with
`cd /home/claude/formalization && export PATH=$HOME/.elan/bin:$PATH && lake env lean <your file>`
(`sorry` only in the two theorems).
